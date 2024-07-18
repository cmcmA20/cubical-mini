{-# OPTIONS --safe #-}
module Meta.Effect.Map where

open import Foundations.Base

open import Meta.Effect.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Map (M : Effect) : Typeω where
  private module M = Effect M
  field
    map : (A → B) → M.₀ A → M.₀ B

open Map ⦃ ... ⦄ public


module _ {M : Effect} (let module M = Effect M) ⦃ _ : Map M ⦄ where
  infixl 4 _<$>_ _<&>_
  _<$>_ : (A → B) → M.₀ A → M.₀ B
  f <$> x = map f x

  _<$_ : B → M.₀ A → M.₀ B
  c <$ x = map (λ _ → c) x

  _<&>_ : M.₀ A → (A → B) → M.₀ B
  x <&> f = map f x

module _ {M N : Effect} (let module M = Effect M; module N = Effect N)
         ⦃ _ : Map M ⦄ ⦃ _ : Map N ⦄ where

  _<<$>>_ : (A → B) → M.₀ (N.₀ A) → M.₀ (N.₀ B)
  f <<$>> a = (f <$>_) <$> a

  _<<&>>_ : M.₀ (N.₀ A) → (A → B) → M.₀ (N.₀ B)
  x <<&>> f = f <<$>> x


instance
  Map-Erased : Map (eff λ T → Erased T)
  Map-Erased .map f (erase x) .erased = f x
