module System.IO.Finite where

open import Foundations.Base

open import Data.String.Base

open import Meta.Show

open import System.IO.Base

postulate
  getLine     : IO′ String
  readFile    : String → IO′ String
  writeFile   : String → String → IO′ ⊤
  appendFile  : String → String → IO′ ⊤
  putStr      : String → IO′ ⊤
  putStrLn    : String → IO′ ⊤

{-# FOREIGN GHC import qualified Data.Text    as T   #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# FOREIGN GHC import qualified System.IO           #-}
{-# FOREIGN GHC import qualified Control.Exception   #-}

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

{-# COMPILE GHC getLine    = TIO.getLine               #-}
{-# COMPILE GHC readFile   = readFiniteFile            #-}
{-# COMPILE GHC writeFile  = TIO.writeFile . T.unpack  #-}
{-# COMPILE GHC appendFile = TIO.appendFile . T.unpack #-}
{-# COMPILE GHC putStr     = TIO.putStr                #-}
{-# COMPILE GHC putStrLn   = TIO.putStrLn              #-}

private variable
  ℓ : Level
  A : Type ℓ

get-line : IO String
get-line = lift getLine

read-file : String → IO String
read-file f = lift (readFile f)

write-file : String → String → IO (Lift ℓ ⊤)
write-file f s = io-lift′ (writeFile f s)

append-file : String → String → IO (Lift ℓ ⊤)
append-file f s = io-lift′ (appendFile f s)

put-str : String → IO (Lift ℓ ⊤)
put-str s = io-lift′ (putStr s)

put-str-ln : String → IO (Lift ℓ ⊤)
put-str-ln s = io-lift′ (putStrLn s)

print : ⦃ Show A ⦄ → A → IO (Lift ℓ ⊤)
print x = put-str-ln (show x)
