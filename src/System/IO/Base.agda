{-# OPTIONS --guarded #-}
module System.IO.Base where

open import Foundations.Base

open import Data.Delay.Base
open import Data.String.Base

open import Agda.Builtin.IO
  renaming (IO to IO′)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

infixl 1 _bind-builtin_

postulate
  return-builtin : A → IO′ A
  _bind-builtin_  : IO′ A → (A → IO′ B) → IO′ B

{-# COMPILE GHC return-builtin = \_ _ -> return    #-}
{-# COMPILE GHC _bind-builtin_  = \_ _ _ _ -> (>>=) #-}

data IO (A : Type ℓ) : Type (ℓsuc ℓ) where
  lift   : (m : IO′ A) → IO A
  return : (x : A) → IO A
  bind   : {B : Type ℓ} (m : ▹ (IO B)) (f : (x : B) → ▹ (IO A)) → IO A
  seq    : {B : Type ℓ} (m₁ : ▹ (IO B)) (m₂ : ▹ (IO A)) → IO A

-- TODO compile as Flat and Sharp
private
  postulate
    force : ▹ A → A
  {-# COMPILE GHC force = \ _ _ f -> f () #-}

-- TODO investigate this
{-# TERMINATING #-}
io-lift : IO A → IO (Lift ℓ′ A)
io-lift      (lift m) = lift (m bind-builtin λ a → return-builtin (lift a))
io-lift      (return a) = return (lift a)
io-lift {ℓ′} (bind m f) = bind (next (io-lift {ℓ′ = ℓ′} (force m)))
                               (λ x → next (io-lift (force (f (lower x)))))
io-lift {ℓ′} (seq m₁ m₂) = seq (next (io-lift {ℓ′ = ℓ′} (force m₁)))
                               (next (io-lift (force m₂)))


{-# NON_TERMINATING #-}
run : IO A → IO′ A
run (lift m) = m
run (return x) = return-builtin x
run (bind m f) = run (force m) bind-builtin λ x → run (force (f x))
run (seq m₁ m₂) = run (force m₁) bind-builtin λ _ → run (force m₂)




-- postulate
--   getLine  : IO String
--   putStrLn : String → IO ⊤

-- {-# FOREIGN GHC import qualified Data.Text    as T   #-}
-- {-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
-- {-# FOREIGN GHC import qualified System.IO           #-}
-- {-# FOREIGN GHC import qualified Control.Exception   #-}

-- {-# COMPILE GHC getLine  = TIO.getLine               #-}
-- {-# COMPILE GHC putStrLn = TIO.putStrLn              #-}

-- main : IO ⊤
-- main = run do
--   lift (putStrLn "lol")
