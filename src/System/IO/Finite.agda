module System.IO.Finite where

open import Foundations.Base

open import Data.String.Base
open import Data.List.Base

open import Meta.Show

open import System.IO.Base

postulate
  getLine     : IO String
  readFile    : String → IO String
  writeFile   : String → String → IO ⊤
  appendFile  : String → String → IO ⊤
  putStr      : String → IO ⊤
  putStrLn    : String → IO ⊤
  getCmdLine  : IO (List String)

{-# FOREIGN GHC import qualified Data.Text    as T        #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TIO      #-}
{-# FOREIGN GHC import qualified System.IO                #-}
{-# FOREIGN GHC import qualified Control.Exception        #-}
{-# FOREIGN GHC import qualified System.Environment as SE #-}

{-# FOREIGN GHC

  -- Reads a finite file. Raises an exception if the file path refers
  -- to a non-physical file (like "/dev/zero").
  readFiniteFile :: T.Text -> IO T.Text
  readFiniteFile f = do
    h <- System.IO.openFile (T.unpack f) System.IO.ReadMode
    Control.Exception.bracketOnError (return ()) (\_ -> System.IO.hClose h)
                                                 (\_ -> System.IO.hFileSize h)
    TIO.hGetContents h

#-}

{-# COMPILE GHC getLine    = TIO.getLine                  #-}
{-# COMPILE GHC readFile   = readFiniteFile               #-}
{-# COMPILE GHC writeFile  = TIO.writeFile . T.unpack     #-}
{-# COMPILE GHC appendFile = TIO.appendFile . T.unpack    #-}
{-# COMPILE GHC putStr     = TIO.putStr                   #-}
{-# COMPILE GHC putStrLn   = TIO.putStrLn                 #-}
{-# COMPILE GHC getCmdLine = (fmap T.pack) <$> SE.getArgs #-}

private variable
  ℓ : Level
  A : Type ℓ

get-line : IO String
get-line = getLine

read-file : String → IO String
read-file f = readFile f

write-file : String → String → IO ⊤
write-file f s = writeFile f s

append-file : String → String → IO ⊤
append-file f s = appendFile f s

put-str : String → IO ⊤
put-str s = putStr s

put-str-ln : String → IO ⊤
put-str-ln s = putStrLn s

print : ⦃ Show A ⦄ → A → IO ⊤
print x = put-str-ln (show x)

get-cmd-line : IO (List String)
get-cmd-line = getCmdLine
