{-# OPTIONS --erased-cubical --guardedness #-}

module Cubical.IO.Base where

open import Agda.Builtin.Coinduction
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit.Base
open import Cubical.Data.Bool.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Sum.Base
import Cubical.IO.Primitive as Prim

private
  variable
    ℓᵃ ℓᵇ : Level
    A : Type ℓᵃ
    B : Type ℓᵇ

------------------------------------------------------------------------
-- The IO monad

-- One cannot write "infinitely large" computations with the
-- postulated IO monad in IO.Primitive without turning off the
-- termination checker (or going via the FFI, or perhaps abusing
-- something else). The following coinductive deep embedding is
-- introduced to avoid this problem. Possible non-termination is
-- isolated to the run function below.

data IO (A : Type ℓᵃ) : Type (ℓ-suc ℓᵃ) where
  lift : (m : Prim.IO A) → IO A
  pure : (x : A) → IO A
  bind : {B : Type ℓᵃ} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  seq  : {B : Type ℓᵃ} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

lift! : ∀ {ℓᵇ} → IO A → IO (Lift {j = ℓᵇ} A)
lift!           (lift io)  = lift (io Prim.>>= λ a → Prim.pure (lift a))
lift!           (pure a)   = pure (lift a)
lift! {ℓᵇ = ℓᵇ} (bind m f) = bind (♯ lift! {ℓᵇ = ℓᵇ} (♭ m))
                                  (λ x → ♯ lift! (♭ (f (lower x))))
lift! {ℓᵇ = ℓᵇ} (seq m₁ m₂) = seq (♯ lift! {ℓᵇ = ℓᵇ} (♭ m₁))
                                  (♯ lift! (♭ m₂))

module _ {A B : Type ℓᵃ} where

  infixl 1 _<$>_ _<*>_ _>>=_ _>>_
  infixr 1 _=<<_

  _<*>_ : IO (A → B) → IO A → IO B
  mf <*> mx = bind (♯ mf) λ f → ♯ (bind (♯ mx) λ x → ♯ pure (f x))

  _<$>_ : (A → B) → IO A → IO B
  f <$> m = pure f <*> m

  _<$_ : B → IO A → IO B
  b <$ m = (const b) <$> m

  _>>=_ : IO A → (A → IO B) → IO B
  m >>= f = bind (♯ m) λ x → ♯ f x

  _=<<_ : (A → IO B) → IO A → IO B
  _=<<_ = flip _>>=_

  _>>_ : IO A → IO B → IO B
  m₁ >> m₂ = seq (♯ m₁) (♯ m₂)

  _<<_ : IO B → IO A → IO B
  _<<_ = flip _>>_

------------------------------------------------------------------------
-- Running programs

-- A value of type `IO A` is a description of a computation that may
-- eventually produce an `A`. The `run` function converts this description
-- of a computation into calls to primitive functions that will actually
-- perform it.

{-# NON_TERMINATING #-}
run : IO A → Prim.IO A
run (lift m)    = m
run (pure x)    = Prim.pure x
run (bind m f)  = run (♭ m ) Prim.>>= λ x → run (♭ (f x))
run (seq m₁ m₂) = run (♭ m₁) Prim.>>= λ _ → run (♭ m₂)

-- The entrypoint of an Agda program will be assigned type `Main` and
-- implemented using `run` on some `IO ⊤` program.

Main : Type₀
Main = Prim.IO {_} Unit*

------------------------------------------------------------------------
-- Utilities

-- Make a unit-returning primitive level polymorphic
lift′ : Prim.IO Unit → IO {ℓᵃ} Unit*
lift′ io = lift (io Prim.>>= λ _ → Prim.pure _)

-- Throw away the result
ignore : IO A → IO Unit*
ignore io = io >> pure _

-- Conditional executions
when : Bool → IO {ℓᵃ} Unit* → IO Unit*
when true m = m
when false _ = pure _

unless : Bool → IO {ℓᵃ} Unit* → IO Unit*
unless = when ∘ not

whenJust : Maybe A → (A → IO {ℓᵃ} Unit*) → IO Unit*
whenJust (just a) k = k a
whenJust nothing  _ = pure _

-- Keep running an IO action until we get a value. Convenient when user
-- input is involved and it may be malformed.
untilJust : IO (Maybe A) → IO A
-- Note that here we are forced to use `bind` & the musical notation
-- explicitly to guarantee that the corecursive call is guarded
untilJust m = bind (♯ m) λ where
  nothing  → ♯ untilJust m
  (just a) → ♯ pure a

untilRight : {A B : Type ℓᵃ} → (A → IO (A ⊎ B)) → A → IO B
untilRight f x = bind (♯ f x) λ where
  (inl x′) → ♯ untilRight f x′
  (inr y)  → ♯ pure y
