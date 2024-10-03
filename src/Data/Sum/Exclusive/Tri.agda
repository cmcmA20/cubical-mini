{-# OPTIONS --safe #-}
module Data.Sum.Exclusive.Tri where

open import Foundations.Base

open import Data.Bool.Base using (Bool; false; true)
open import Data.Empty.Base using ()
open import Data.Dec.Base using (Dec; no; yes; ⌊_⌋)

data Tri {ℓ ℓ′ ℓ″} (P : 𝒰 ℓ) (Q : 𝒰 ℓ′) (R : 𝒰 ℓ″) : 𝒰 (ℓ ⊔ ℓ′ ⊔ ℓ″) where
  inxl :   P → ¬ Q → ¬ R → Tri P Q R
  inxm : ¬ P →   Q → ¬ R → Tri P Q R
  inxr : ¬ P → ¬ Q →   R → Tri P Q R

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A P Q R : Type ℓ

elim : {M : Tri P Q R → 𝒰 ℓ}
     → (( p :   P) (¬q : ¬ Q) (¬r : ¬ R) → M (inxl  p ¬q ¬r))
     → ((¬p : ¬ P) ( q :   Q) (¬r : ¬ R) → M (inxm ¬p  q ¬r))
     → ((¬p : ¬ P) (¬q : ¬ Q) ( r :   R) → M (inxr ¬p ¬q  r))
     → (t : Tri P Q R) → M t
elim tp _  _  (inxl  p ¬q ¬r) = tp  p ¬q ¬r
elim _  tq _  (inxm ¬p  q ¬r) = tq ¬p  q ¬r
elim _  _  tr (inxr ¬p ¬q  r) = tr ¬p ¬q  r

rec : A → A → A → Tri P Q R → A
rec p q r = elim (λ _ _ _ → p) (λ _ _ _ → q) (λ _ _ _ → r)

tri→dec-l : Tri P Q R → Dec P
tri→dec-l = elim (λ p _ _ → yes p) (λ ¬p _ _ → no ¬p) (λ ¬p _ _ → no ¬p)

tri→dec-m : Tri P Q R → Dec Q
tri→dec-m = elim (λ _ ¬q _ → no ¬q) (λ _ q _ → yes q) (λ _ ¬q _ → no ¬q)

tri→dec-r : Tri P Q R → Dec R
tri→dec-r = elim (λ _ _ ¬r → no ¬r) (λ _ _ ¬r → no ¬r) (λ _ _ r → yes r)

is-inxl? is-inxm? is-inxr? : Tri P Q R → Bool
is-inxl? = ⌊_⌋ ∘ tri→dec-l
is-inxm? = ⌊_⌋ ∘ tri→dec-m
is-inxr? = ⌊_⌋ ∘ tri→dec-r
