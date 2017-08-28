{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Applicative    ((<$>))
import           Control.Monad          (forM_)
import           Control.Monad          (when)
import qualified Data.ByteString.Char8  as BS
import qualified Data.ByteString.Lazy   as BL
import           Data.ByteString.Search (replace)
import qualified Data.IORef             as IOR
import           System.Directory       (canonicalizePath, copyFile,
                                         doesFileExist, setCurrentDirectory)
import           System.Environment     (getArgs, setEnv, getEnv)
import           System.FilePath        (replaceDirectory, splitDirectories,
                                         takeBaseName, takeDirectory, (</>))
import           System.IO.Temp         (withSystemTempDirectory)
import           System.Process         (readProcessWithExitCode)
import           Text.Regex.TDFA        ((=~))
import qualified Control.Exception      as E
import           Data.Typeable               (Typeable)

data CheckerResult =
  CheckerFound
  | CheckerNotFound

data UnexpectedState = UnexpectedState String deriving (Typeable)
instance E.Exception UnexpectedState

instance Show UnexpectedState where
  show (UnexpectedState msgstr) = "UnexpectedState: " ++ msgstr

headRaise :: [a] -> IO a
headRaise [] = E.throw (UnexpectedState "head failed")
headRaise (x:_) = return x

headMaybe :: [a] -> IO (Maybe a)
headMaybe [] = return Nothing
headMaybe (x:_) = return (Just x)

processResult :: FilePath -> (t, String, String) -> IO CheckerResult
processResult source_file (code, stdout, stderr) = do
  let rlines = BS.lines (BS.pack stderr)
  BS.putStr (BS.pack stdout)
  top_include <- IOR.newIORef Nothing
  forM_ rlines $ \line -> do
    case ((line =~ ("^(In file included from |                 from )([^:]+)[:]([0-9]+)"
                    :: BS.ByteString)) :: [[BS.ByteString]]) of
       [[_, _, filename, line_nr]] -> IOR.writeIORef top_include (Just (filename, line_nr))
       _ -> return ()
    case ((line =~ ("^([^:]+)[:] At top level:"
                    :: BS.ByteString)) :: [[BS.ByteString]]) of
       [[_, _]] -> IOR.writeIORef top_include Nothing
       _ -> case ((line =~ ("^([^:]+)([:][0-9]+[:][0-9]+[:]) ((fatal error|warning|error)[:])( .*)"
                    :: BS.ByteString)) :: [[BS.ByteString]]) of
            [[_, filename_in_line, location, prefix, _, rest_of_line]] ->
                do  included_from <- IOR.readIORef top_include
                    case (included_from, filename_in_line /= (BS.pack source_file)) of
                       (Just (filename, line_nr), True) ->
                         BS.putStrLn $ BS.concat [ filename, ":", line_nr, ":1: ",
                                                   prefix, " (included) ",
                                                   filename_in_line, location, rest_of_line]
                       _ -> return ()
                    return ()
            _ -> return ()

    BS.putStrLn line
  return CheckerFound

compilerInvokeEnv :: String -> String -> [String] -> [BS.ByteString] -> IO CheckerResult
compilerInvokeEnv tmp_file cdir env stdparams = do
  let find_c x = if (not ("-" `BS.isPrefixOf` x)) && (".c" `BS.isSuffixOf` x) then BS.pack tmp_file else x
  let map_1 = map find_c stdparams
  let params =  map_1 ++ ["-fsyntax-only", "-fno-diagnostics-show-caret",
                          "-fno-diagnostics-color", "-iquote", BS.pack cdir]
  let str_params = BS.unwords params
  BS.putStrLn str_params
  (code, stdout, stderr) <- readProcessWithExitCode "env" (env ++ ["LC_ALL=C", "bash", "-c", BS.unpack str_params]) ""
  processResult tmp_file (code, stdout, stderr)

compilerInvoke :: String -> String -> [BS.ByteString] -> IO CheckerResult
compilerInvoke tmp_file cdir stdparams = do
  compilerInvokeEnv tmp_file cdir [] stdparams

upmostDirectoryToSatisify :: FilePath -> (FilePath -> IO Bool) -> IO (Maybe FilePath)
upmostDirectoryToSatisify dir func = do
   b <- func dir
   upperRes <- if dir == "/" then return Nothing
                             else upmostDirectoryToSatisify (takeDirectory dir) func
   case upperRes of
       Just dir -> return $ Just dir
       Nothing -> return $ if b then Just dir else Nothing


linuxChecker :: FilePath -> FilePath -> IO CheckerResult
linuxChecker tmp_file orig_src_file = do
  --
  -- Checker able to deal with source files of configured and
  -- built Linux kernel trees, or external kernel modules to
  -- those trees.
  --
  let dir = takeDirectory orig_src_file
  cdir <- canonicalizePath dir
  tmp_file_canonized <- canonicalizePath tmp_file

  -- Find the .*.o.cmd file
  let base = takeBaseName orig_src_file
  let cmdfile = dir ++ "/." ++ base ++ ".o.cmd"
  e <- doesFileExist cmdfile
  E.catch (
    do
      -- Now we can know the compiler's command line, but we need to sanitize
      -- it a little.
      content <- BS.readFile cmdfile
      let flines = BS.lines content
      headFlines <- headRaise flines
      let (key, val) = BS.breakSubstring " := " headFlines
      let split = BS.split ' ' $ BS.drop 4 val
      let filter_1 = filter (not . (BS.isPrefixOf "-Wp,")) split

      -- Fixup for RH 7
      env <- if filter (== "/opt/rh/devtoolset-3/root/usr/lib/gcc/x86_64-redhat-linux/4.9.2/include") split /= [] then
        do
          path <- getEnv "PATH"
          return ["PATH=/opt/rh/devtoolset-3/root/bin:" ++ path]
        else
          return []
      --
      -- Find the location of the kernel tree, as we must have it in order
      -- to build a kernel module.
      --
      -- For internal modules, the path is relative, so it is trivial.
      -- For external modules, there's more difficulty. On older trees
      -- there is an include to kconfig.h that can tell us, but on newer
      -- kernels such information only exists in the resulting .ko, which
      -- is too late in the build process.
      --
      -- A slight modification to an external kernel module Makefile can
      -- pass a '-D__ORIG_KDIR__=' as a harmless addition to the command line,
      -- we can use it as a mini-protocol.
      --
      kdirFile <- doesFileExist ".kdir"
      kernel_dir <-
        if kdirFile
          then fmap BS.unpack $ BS.readFile ".kdir"
          else do
                kconfig <- headRaise $ filter (BS.isSuffixOf "/include/linux/kconfig.h") filter_1

                let orig_kdir_prefix = "-D__ORIG_KDIR__="
                morig_kdir <- headMaybe $ filter (orig_kdir_prefix `BS.isPrefixOf`) filter_1
                case morig_kdir of
                    Just orig_kdir -> return $
                      if | not ("cmd_/" `BS.isPrefixOf` key) -> -- Internal kernel tree code!
                             (iterate takeDirectory orig_src_file) !! (length $ splitDirectories $ BS.unpack $ BS.drop 5 key)
                         | "/" `BS.isPrefixOf` kconfig ->
                             takeDirectory $ takeDirectory $ takeDirectory $ BS.unpack $ kconfig
                         | otherwise ->
                             BS.unpack $ BS.drop (BS.length orig_kdir_prefix) orig_kdir
                    Nothing -> do
                        m <- upmostDirectoryToSatisify cdir $ \dir -> do
                            e1 <- doesFileExist $ dir ++ "/Makefile"
                            e2 <- doesFileExist $ dir ++ "/Kbuild"
                            e3 <- doesFileExist $ dir ++ "/Kconfig"
                            e4 <- doesFileExist $ dir ++ "/README"
                            return $ e1 && e2 && e3 && e4
                        case m of
                            Nothing -> E.throw (UnexpectedState "no kernel tree found")
                            Just x -> return x

      setCurrentDirectory kernel_dir
      let fixslash x = BS.concat $ BL.toChunks $ replace "\\#" ("#" :: BL.ByteString) x
      compilerInvokeEnv tmp_file_canonized cdir env (map fixslash filter_1)
    ) (\(e :: E.SomeException) -> return CheckerNotFound)

makefileChecker :: FilePath -> FilePath -> IO CheckerResult
makefileChecker tmp_file orig_src_file = do
  abs_src_file <- canonicalizePath orig_src_file
  check abs_src_file abs_src_file
  where
    check root dir = do
      e <- doesFileExist $ dir </> "Makefile"
      if e
        then do
           let pac_flycheck_file = dir </> ".pac-flycheck"
           flagsFileExists <- doesFileExist pac_flycheck_file
           flags <- if flagsFileExists
                    then map BS.unpack . BS.lines <$> BS.readFile pac_flycheck_file
                    else return []
           let
             params =
                 [ "check-syntax"
                 , "-C", dir
                 , "CHK_SOURCES=" ++ tmp_file
                 , "LC_ALL=C"
                 , "QUOTE_INCLUDE_DIRS=" ++ (show (takeDirectory root))
                 ] ++ flags

           putStrLn $ "+ make " ++ unwords params
           (code, stdout, stderr) <- readProcessWithExitCode "make" params ""
           processResult tmp_file (code, stdout, stderr)
        else do
           if dir == "/"
             then return CheckerNotFound
             else check root $ takeDirectory dir

standaloneChecker :: FilePath -> FilePath -> IO CheckerResult
standaloneChecker tmp_file orig_src_file = do
  let dir = takeDirectory orig_src_file
  cdir <- canonicalizePath dir
  let is_c =".c" `BS.isSuffixOf` (BS.pack orig_src_file)
  let is_cpp =".cpp" `BS.isSuffixOf` (BS.pack orig_src_file)
  if is_c || is_cpp
    then
    do let params = map BS.pack [if is_c then "gcc" else "g++",
                                 if is_c then "-std=gnu11" else "-std=c++11", "-O2", "-Wall",
                                 "-Wextra", "-o", "a.o", orig_src_file, "-c"]
       compilerInvoke tmp_file cdir params
    else
      return CheckerNotFound

mainIndirect :: (String -> Bool) -> FilePath -> FilePath -> IO ()
mainIndirect f tmp_file orig_src_file =
  -- TODO: check for .c and .cc/.cpp extensions
  do let
       checkers = [
             ("linux", linuxChecker)
           , ("makefile", makefileChecker)
           , ("standalone", standaloneChecker)
         ]
     testCheckers checkers
  where testCheckers [] = return ()
        testCheckers ((name, checker):others) = do
          if f name then do
            r <- checker tmp_file orig_src_file
            case r of
              CheckerNotFound -> testCheckers others
              CheckerFound -> return ()
            else
              testCheckers others

mainViaTmp :: (String -> Bool) -> FilePath -> IO ()
mainViaTmp f src_file =
  withSystemTempDirectory "pacXXXXXX" $ \dir -> do
    let tmp_file = replaceDirectory src_file dir
    copyFile src_file tmp_file
    mainIndirect f tmp_file src_file

main :: IO ()
main = do
  args <- getArgs
  case args of
    [src_file] -> mainViaTmp (const True) src_file
    ["--direct", direct_file] -> mainIndirect (const True) direct_file direct_file
    ['c':'h':'e':'c':'k':'e':'r':':':xs, src_file] -> mainViaTmp (== xs) src_file
    [tmp_file, orig_src_file] -> mainIndirect (const True) tmp_file orig_src_file
    _ -> putStrLn $ "Cannot work with argument " ++ (show args)
