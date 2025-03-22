{-# OPTIONS --safe #-}
module Meta.Effect.Map.Base where

open import Foundations.Base

open import Meta.Effect.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Map (M : Effect) : Typeω where
  private module M = Effect M
  field map : (A → B) → M.₀ A → M.₀ B
open Map ⦃ ... ⦄

module _ {M : Effect} (let module M = Effect M) ⦃ _ : Map M ⦄ where
  infixl 4 _<$>_ _<&>_
  _<$>_ : (A → B) → M.₀ A → M.₀ B
  f <$> x = map f x

  _<$_ : B → M.₀ A → M.₀ B
  c <$ x = map (λ _ → c) x

  _<&>_ : M.₀ A → (A → B) → M.₀ B
  x <&> f = map f x

  instance
    Funlike-Effect-Map
      : ∀ {ℓᵃ ℓᵇ} {A : Type ℓᵃ} {B : Type ℓᵇ}
      → Funlike ur (Type ℓᵃ → Type (M.adj ℓᵃ)) (A → B) λ (_ , f) → M.₀ A → M.₀ B
    Funlike-Effect-Map ._#_ _ = map


module _ {M N : Effect} (let module M = Effect M; module N = Effect N)
         ⦃ _ : Map M ⦄ ⦃ _ : Map N ⦄ where

  _<<$>>_ : (A → B) → M.₀ (N.₀ A) → M.₀ (N.₀ B)
  f <<$>> a = (f <$>_) <$> a

  _<<&>>_ : M.₀ (N.₀ A) → (A → B) → M.₀ (N.₀ B)
  x <<&>> f = f <<$>> x

  Map-Compose : Map (eff (M.₀ ∘ N.₀))
  Map-Compose .map = _<<$>>_

instance
  Map-Erased : Map (eff λ T → Erased T)
  Map-Erased .map f (erase x) .erased = f x

-- TODO search is busted
Map-Id : Map (eff id)
Map-Id .map f x = f x

