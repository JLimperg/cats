{-# LANGUAGE PatternGuards #-}

import qualified Data.List as List
import           System.Environment
  (getArgs)
import           System.Exit
  (exitFailure)
import           System.FilePath
  ((</>), dropExtension, isPathSeparator, makeRelative)
import           System.FilePath.Find
  (find, always, (==?), (||?), extension)
import           System.IO
  (hPutStr, stderr, withFile, IOMode(..), hSetEncoding, utf8)


outputFile, srcDir :: FilePath
outputFile = "Everything.agda"
srcDir     = "."


main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  modules <- List.sort . filter (/= srcDir </> outputFile) <$>
               find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    srcDir
  writeFileUTF8 outputFile $ format modules


-- | Usage info.
usage :: String
usage = unlines
  [ "GenerateEverything: A utility program for Agda's standard library."
  , ""
  , "Usage: everything"
  , ""
  , "This program should be run in the base directory of a clean checkout of"
  , "the library."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to "
  , outputFile ++ "."
  ]


-- | Formats the extracted module information.
format :: [FilePath] -> String
format = unlines . map fmt
  where
    fmt m = "import " ++ fileToMod m


-- | Translates a file name to the corresponding module name. It is
-- assumed that the file name corresponds to an Agda module under
-- 'srcDir'.
fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c


-- | A variant of 'writeFile' which uses the 'utf8' encoding.
writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s
