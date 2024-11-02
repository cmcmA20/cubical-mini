{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom

open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Instances.Map public

private variable
  @0 n : ℕ
  ℓ : Level
  A B : Type ℓ

_<*>ᵥ_ : Vec (A → B) n → Vec A n → Vec B n
[]       <*>ᵥ _        = []
(f ∷ fs) <*>ᵥ (x ∷ xs) = f x ∷ (fs <*>ᵥ xs)

instance
  Idiom-Vec : ∀ {n} → Idiom (eff (λ T → Vec T n))
  Idiom-Vec .pure = replicate _
  Idiom-Vec ._<*>_ = _<*>ᵥ_

  Lawful-Idiom-Vec : ∀ {n} → Lawful-Idiom (eff (λ T → Vec T n))
  Lawful-Idiom-Vec .pure-id {A} {v} = go v where opaque
    go : ∀ {n} → (xs : Vec A n) → (pure id <*> xs) ＝ xs
    go {0}     []       = refl
    go {suc n} (x ∷ xs) = ap (x ∷_) (go xs)
  Lawful-Idiom-Vec .pure-pres-app {f} {x} = go where opaque
    go : ∀ {n} → (pure f <*> pure x) ＝ replicate n (f x)
    go {0}     = refl
    go {suc n} = ap (_ ∷_) go
  Lawful-Idiom-Vec .pure-interchange {A} {B} {u} {v} = go u v where opaque
    go : ∀ {n} → (fs : Vec (A → B) n) (x : A) → (fs <*> pure x) ＝ (pure (_$ x) <*> fs)
    go {0}     []       x = refl
    go {suc n} (f ∷ fs) x = ap (_ ∷_) (go fs x)
  Lawful-Idiom-Vec .pure-comp {A} {B} {C} {u} {v} {w} = go u v w where opaque
    go : ∀ {n} → (gs : Vec (B → C) n) (fs : Vec (A → B) n) (xs : Vec A n)
       → (pure _∘ˢ_ <*> gs <*> fs <*> xs) ＝ (gs <*> (fs <*> xs))
    go {0}     []       fs       _        = refl
    go {suc n} (g ∷ gs) (f ∷ fs) (x ∷ xs) = ap (_ ∷_) (go gs fs xs)
