{-# OPTIONS --safe #-}
module Data.Sum.Exclusive.Properties where

open import Foundations.Prelude

open import Meta.Extensionality
open import Meta.Marker

open import Functions.Embedding

open import Data.Empty.Base as ⊥
open import Data.Sum.Base as ⊎
open import Data.Sum.Properties using (⊎↪)
open import Data.Sum.Exclusive.Base as ⊻
open import Data.Sum.Exclusive.Path as ⊻

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

universal : {ℓᵃ ℓᵇ ℓᶜ : Level} {A : Type ℓᵃ} {B : Type ℓᵇ}
            {C : A ⊻ B → Type ℓᶜ}
          → (Π[ x ꞉ A ⊻ B ] C x)
          ≃ ( (Π[ a ꞉ A ] Π[ ¬b ꞉ ¬ B ] C (inxl a ¬b))
            × (Π[ b ꞉ B ] Π[ ¬a ꞉ ¬ A ] C (inxr b ¬a))
            )
universal = ≅→≃ the-iso where
  open Iso
  the-iso : _ ≅ _
  the-iso .to f = (λ a ¬b → f (inxl a ¬b)) , (λ b ¬a → f (inxr b ¬a))
  the-iso .from (f , g) (inxl a ¬a) = f a ¬a
  the-iso .from (f , g) (inxr b ¬b) = g b ¬b
  the-iso .inverses .Inverses.inv-o = refl
  the-iso .inverses .Inverses.inv-i i f (inxl a ¬b) = f (inxl a ¬b)
  the-iso .inverses .Inverses.inv-i i f (inxr b ¬a) = f (inxr b ¬a)

⊻-ap : A ≃ B → C ≃ D → (A ⊻ C) ≃ (B ⊻ D)
⊻-ap f g = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to = qmap (f #_) (λ ¬a b → ¬a (f ⁻¹ $ b)) (g #_) (λ ¬c d → ¬c (g ⁻¹ $ d))
  from = [ (λ b ¬d → inxl (f ⁻¹ $ b) (¬d ∘ g #_)) , (λ d ¬b → inxr (g ⁻¹ $ d) (¬b ∘ f #_)) ]ₓ
  ri : _
  ri (inxl b ¬d) = ap² inxl (Equiv.ε f b) prop!
  ri (inxr d ¬b) = ap² inxr (Equiv.ε g d) prop!
  li : _
  li (inxl a ¬c) = ap² inxl (Equiv.η f a) prop!
  li (inxr c ¬a) = ap² inxr (Equiv.η g c) prop!

⊻-ap-l : A ≃ B → (A ⊻ C) ≃ (B ⊻ C)
⊻-ap-l f = ⊻-ap f refl

⊻-ap-r : B ≃ C → (A ⊻ B) ≃ (A ⊻ C)
⊻-ap-r f = ⊻-ap refl f

⊻-comm : (A ⊻ B) ≃ (B ⊻ A)
⊻-comm = ≅→≃ $ iso go go (fun-ext i) (fun-ext i) where
  go : {A : Type ℓᵃ} {B : Type ℓᵇ} → (A ⊻ B) → (B ⊻ A)
  go = [ inxr , inxl ]ₓ
  i : {A : Type ℓᵃ} {B : Type ℓᵇ} (x : A ⊻ B) → go (go x) ＝ x
  i (inxl _ _) = refl
  i (inxr _ _) = refl

⊻≃×¬⊎×¬ : (A ⊻ B) ≃ (A × (¬ B) ⊎ B × (¬ A))
⊻≃×¬⊎×¬ = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to = [ curry² inl , curry² inr ]ₓ
  from = [ inxl $²_ , inxr $²_ ]ᵤ
  ri : _
  ri (inl _) = refl
  ri (inr _) = refl
  li : _
  li (inxl _ _) = refl
  li (inxr _ _) = refl

⊻↪⊎ : (A ⊻ B) ↪ (A ⊎ B)
⊻↪⊎ = ≃→↪ ⊻≃×¬⊎×¬ ∙ ⊎↪ (fst , subset-proj-is-embedding (λ _ → hlevel 1)) (fst , subset-proj-is-embedding (λ _ → hlevel 1))

⊻-is-of-size : is-of-size ℓᶜ A → is-of-size ℓᵈ B
             → is-of-size (ℓᶜ ⊔ ℓᵈ) (A ⊻ B)
⊻-is-of-size {ℓᶜ} {ℓᵈ} (A , as) (B , bs) = A ⊻ B , ⊻-ap as bs

instance
  Size-⊻ : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
           ⦃ sa : Size ℓᶜ A ⦄
           ⦃ sb : Size ℓᵈ B ⦄
         → Size (ℓᶜ ⊔ ℓᵈ) (A ⊻ B)
  Size-⊻ {ℓᶜ} {ℓᵈ} .Size.has-of-size = ⊻-is-of-size (size ℓᶜ) (size ℓᵈ)
