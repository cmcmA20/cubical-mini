{-# OPTIONS --safe #-}
module Meta.Effect.Idiom where

open import Foundations.Base

open import Meta.Effect.Map public

open import Data.Bool.Base

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : A → M.₀ A
    _<*>_ : M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_

open Idiom ⦃ ... ⦄ public


module _ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄ where
  when : Bool → M.₀ ⊤ → M.₀ ⊤
  when true  t = t
  when false _ = pure tt

  unless : Bool → M.₀ ⊤ → M.₀ ⊤
  unless false t = t
  unless true  _ = pure tt

  map² : (A → B → C) → M.₀ A → M.₀ B → M.₀ C
  map² f x y = ⦇ f x y ⦈

  map³ : (A → B → C → D) → M.₀ A → M.₀ B → M.₀ C → M.₀ D
  map³ f x y z = ⦇ f x y z ⦈

instance
  Idiom-Erased : Idiom (eff λ T → Erased T)
  Idiom-Erased .pure x = erase x
  Idiom-Erased ._<*>_ (erase f) (erase x) .erased = f x

  Idiom-Syntax : ∀ {o a} {𝔽 : Signature o a}
               → Idiom (eff (Syntax 𝔽))
  Idiom-Syntax .pure = var
  Idiom-Syntax {𝔽} ._<*>_ {A} {B} = go where
    go : Syntax 𝔽 (A → B) → Syntax 𝔽 A → Syntax 𝔽 B
    go (var f)          x = map f x
    go (impure (o , k)) x = impure (o , λ i → go (k i) x)
