module System.IO.Base where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Maybe.Base

open import Agda.Builtin.IO public
  renaming (IO to IO′)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

infixl 1 _>>=′_

postulate
  return : A → IO′ A
  _>>=′_  : IO′ A → (A → IO′ B) → IO′ B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=′_  = \_ _ _ _ -> (>>=) #-}

open import Agda.Builtin.Coinduction
  using ()
  renaming ( ∞  to Delay
           ; ♯_ to later
           ; ♭  to force )

data IO (A : Type ℓ) : Type (ℓsuc ℓ) where
  lift : (m : IO′ A) → IO A
  pure : (x : A) → IO A
  bind : {B : Type ℓ} (m : Delay (IO B)) (f : (x : B) → Delay (IO A)) → IO A
  seq  : {B : Type ℓ} (m₁ : Delay (IO B)) (m₂ : Delay (IO A)) → IO A

io-lift : IO A → IO (Lift ℓ′ A)
io-lift           (lift io)   = lift (io >>=′ λ a → return (lift a))
io-lift           (pure a)    = pure (lift a)
io-lift {ℓ′ = ℓ′} (bind m f)  = bind (later (io-lift {ℓ′ = ℓ′} (force m)))
                                     (λ x → later (io-lift (force (f (lower x)))))
io-lift {ℓ′ = ℓ′} (seq m₁ m₂) = seq (later (io-lift {ℓ′ = ℓ′} (force m₁)))
                                    (later (io-lift (force m₂)))

module _ {A B : Type ℓ} where

  infixl 1 _<$>_ _<*>_ _>>=_ _>>_
  infixr 1 _=<<_

  _<*>_ : IO (A → B) → IO A → IO B
  mf <*> mx =
    bind (later mf) λ f → later (bind (later mx) λ x → later (pure (f x)))

  _<$>_ : (A → B) → IO A → IO B
  f <$> m = pure f <*> m

  _<$_ : B → IO A → IO B
  b <$ m = (const b) <$> m

  _>>=_ : IO A → (A → IO B) → IO B
  m >>= f = bind (later m) λ x → later (f x)

  _=<<_ : (A → IO B) → IO A → IO B
  _=<<_ = flip _>>=_

  _>>_ : IO A → IO B → IO B
  m₁ >> m₂ = seq (later m₁) (later m₂)

  _<<_ : IO B → IO A → IO B
  _<<_ = flip _>>_

{-# NON_TERMINATING #-}
run : IO A → IO′ A
run (lift m)    = m
run (pure x)    = return x
run (bind m f)  = run (force m ) >>=′ λ x → run (force (f x))
run (seq m₁ m₂) = run (force m₁) >>=′ λ _ → run (force m₂)

Main : Type
Main = IO′ (Lift 0ℓ ⊤)

io-lift′ : IO′ ⊤ → IO (Lift ℓ ⊤)
io-lift′ m = lift (m >>=′ λ _ → return _)

when : Bool → IO (Lift ℓ ⊤) → IO (Lift ℓ ⊤)
when true  m = m
when false _ = pure _

until-just : IO (Maybe A) → IO A
until-just m = bind (later m) λ where
  nothing  → later (until-just m)
  (just a) → later (pure a)
