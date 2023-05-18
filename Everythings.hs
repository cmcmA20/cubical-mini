import System.Environment
import System.Directory
import System.Exit
import Control.Monad
import Data.Maybe
import Data.List

stripSuffix :: (Eq a) => [a] -> [a] -> Maybe [a]
stripSuffix sfx = fmap reverse . stripPrefix (reverse sfx) . reverse

splitOn :: Char -> String -> [String]
splitOn d = foldr go []
  where go :: Char -> [String] -> [String]
        go x acc | d == x = []:acc
        go x (a:acc) = (x:a):acc
        go x [] = [[x]]

type SplitFilePath   = [String]
type SplitModuleName = [String]

showFP :: Char -> SplitFilePath -> String
showFP c fp = intercalate [c] (reverse fp)

addToFP :: SplitFilePath -> String -> SplitFilePath
addToFP fp dir = dir : fp

prependToPath :: String -> SplitFilePath -> SplitFilePath
prependToPath prefix fp = fp ++ [ prefix ]

moduleToPath :: FilePath -> SplitModuleName -> SplitFilePath
moduleToPath base xs = xs ++ [ base ]

pathToModule :: String -> SplitFilePath -> SplitModuleName
pathToModule base []  = []
pathToModule base [x] = if x == base then [] else [x]
pathToModule base (x : xs) = x : pathToModule base xs

-- Given a path to a directory, returns a pair containing the list of all its
--  subdirectories and the list of all agda files it contains
getSubDirsFiles :: String -> SplitFilePath -> IO ([String], [String])
getSubDirsFiles base fp = do
  ls <- getDirectoryContents ("./" ++ showFP '/' (prependToPath base fp))
  let sub_dirs = filter ('.' `notElem`) ls
      files    = mapMaybe (stripSuffix ".agda") ls
  pure (sub_dirs, files)

-- Given a path to an agda file, returns the list of all modules it imports
getImported :: String -> SplitFilePath -> IO [SplitModuleName]
getImported base fp = do
  ls <- fmap words . lines <$> readFile ("./" ++ base ++ "/" ++ showFP '/' fp ++ ".agda")
  pure $ fmap (reverse . splitOn '.') (mapMaybe f ls)
  where f :: [String] -> Maybe String
        f ("open":"import":x:_) = Just x
        f ("import":x:_) = Just x
        f _ = Nothing

-- Given a path to a directory $fp and a path to an agda file $fileToCheck.agda,
--  returns the list of all modules in* $fp not imported in $fileToCheck.agda
-- * recursively
getMissingModules :: String -> SplitFilePath -> Maybe SplitFilePath -> IO [SplitModuleName]
getMissingModules base fp fpToCheck = do
  (sub_dirs, sub_files) <- getSubDirsFiles base fp
  -- recursively get all files in $fp/X not imported in $fp/X.agda (if it exists)
  missing_modules <- concat <$> forM sub_dirs (\sub_dir ->
    getMissingModules base (addToFP fp sub_dir)
                           (addToFP fp <$> find (== sub_dir) sub_files))
  -- return all of these files, plus all agda files in the current directory,
  --  except for those which are imported in $fpToCheck.agda (if it exists) or
  --  which are $fpToCheck.agda itself
  imported <- maybe (pure []) (getImported base) fpToCheck
  pure $ ((addToFP fp <$> sub_files) ++ missing_modules)
         \\ (maybeToList fpToCheck ++ imported)


checkEverythings :: FilePath -> [String] -> IO ()
checkEverythings base dirs = do
  missing_files <- concat <$> forM dirs (\dir ->
    getMissingModules base [dir] (Just ["Everything",dir]))
  if null missing_files then pure ()
  else do putStrLn "Found some files which are not imported in any Everything.agda:"
          forM_ missing_files (putStrLn . (" " ++) . showFP '.')
          exitFailure

checkREADME :: String -> IO ()
checkREADME base = do
  (sub_dirs, _) <- getSubDirsFiles base []
  let sub_dirs' = sub_dirs \\ ["System"]
  imported <- getImported base ["README"]
  let missing_files = fmap (\dir -> ["Everything",dir]) sub_dirs' \\ imported
  if null missing_files then pure ()
  else do putStrLn "Found some Everything.agda's which are not imported in README.agda:"
          forM_ missing_files (putStrLn . (" " ++) . showFP '.')
          exitFailure

genEverythings :: String -> [SplitFilePath] -> IO ()
genEverythings base =
  mapM_ (\dir -> do
    files <- getMissingModules base dir Nothing
    let ls = [ "{-# OPTIONS --safe #-}"
             , "module " ++ showFP '.' ("Everything" : dir) ++ " where"
             , [] ]
             ++ sort (fmap (\file -> "import " ++ showFP '.' file)
                           (delete (addToFP dir "Everything") files))
    writeFile ("./" ++ base ++ "/" ++ showFP '/' (addToFP dir "Everything") ++ ".agda")
              (unlines ls))


helpText :: String
helpText = unlines [
  "Accepted arguments: ",
  " check d1 d2 ... dn         checks imports in the Everything files in the",
  "                            given directories",
  " check-except d1 d2 ... dn  checks imports in all Everything files except those",
  "                            in the given directories",
  " gen d1 d2 ... dn           generates Everything files in the given directories",
  " gen-except d1 d2 ... dn    generates Everything files in all directories",
  "                            except in those given",
  " check-README               checks all Everything files are imported in README",
  " get-imports-README         gets the list of all Everything files imported in README"]

kek :: String -> SplitFilePath
kek = reverse . splitOn '/'

main :: IO ()
main = do
  let base_dir = "src"
  all_dirs <- filter ('.' `notElem`) <$> getDirectoryContents base_dir
  args <- getArgs
  case args of
    "check":dirs -> checkEverythings base_dir dirs
    "gen"  :dirs -> genEverythings   base_dir (kek <$> dirs)
    "check-except":ex_dirs -> checkEverythings base_dir (all_dirs \\ ex_dirs)
    "gen-except"  :ex_dirs -> genEverythings   base_dir (kek <$> (all_dirs \\ ex_dirs))
    ["check-README"] -> checkREADME base_dir
    ["get-imports-README"] -> do
      imported <- filter (\fp -> head fp == "Everything")
                    <$> getImported base_dir ["README"]
      putStrLn . unwords $ map (\fp -> showFP '/' fp ++ ".agda") imported
    "help":_ -> putStrLn helpText
    _ -> putStrLn "argument(s) not recognized, try 'help'"
