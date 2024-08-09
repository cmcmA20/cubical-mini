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
  the-iso : Iso _ _
  the-iso .fst f = (λ a ¬b → f (inxl a ¬b)) , (λ b ¬a → f (inxr b ¬a))
  the-iso .snd .is-iso.inv (f , g) (inxl a ¬a) = f a ¬a
  the-iso .snd .is-iso.inv (f , g) (inxr b ¬b) = g b ¬b
  the-iso .snd .is-iso.rinv _ = refl
  the-iso .snd .is-iso.linv f i (inxl a ¬b) = f (inxl a ¬b)
  the-iso .snd .is-iso.linv f i (inxr b ¬a) = f (inxr b ¬a)

⊻-ap : A ≃ B → C ≃ D → (A ⊻ C) ≃ (B ⊻ D)
⊻-ap f g = ≅→≃ the-iso where
  the-iso : Iso _ _
  the-iso .fst = qmap (f #_) (λ ¬a b → ¬a (f ⁻¹ $ b)) (g #_) (λ ¬c d → ¬c (g ⁻¹ $ d))
  the-iso .snd .is-iso.inv = [ (λ b ¬d → inxl (f ⁻¹ $ b) (¬d ∘ g #_)) , (λ d ¬b → inxr (g ⁻¹ $ d) (¬b ∘ f #_)) ]ₓ
  the-iso .snd .is-iso.rinv (inxl b ¬d) = ap² inxl (f .snd .equiv-proof b .fst .snd) prop!
  the-iso .snd .is-iso.rinv (inxr d ¬b) = ap² inxr (g .snd .equiv-proof d .fst .snd) prop!
  the-iso .snd .is-iso.linv (inxl a ¬c) = ap² inxl (Equiv.η f a) prop!
  the-iso .snd .is-iso.linv (inxr c ¬a) = ap² inxr (Equiv.η g c) prop!

⊻-ap-l : A ≃ B → (A ⊻ C) ≃ (B ⊻ C)
⊻-ap-l f = ⊻-ap f refl

⊻-ap-r : B ≃ C → (A ⊻ B) ≃ (A ⊻ C)
⊻-ap-r f = ⊻-ap refl f

⊻-comm : (A ⊻ B) ≃ (B ⊻ A)
⊻-comm = ≅→≃ i where
  i : Iso _ _
  i .fst = [ inxr , inxl ]ₓ
  i .snd .is-iso.inv = [ inxr , inxl ]ₓ
  i .snd .is-iso.rinv (inxl _ _) = refl
  i .snd .is-iso.rinv (inxr _ _) = refl
  i .snd .is-iso.linv (inxl _ _) = refl
  i .snd .is-iso.linv (inxr _ _) = refl

⊻≃×¬⊎×¬ : (A ⊻ B) ≃ (A × (¬ B) ⊎ B × (¬ A))
⊻≃×¬⊎×¬ = ≅→≃ i where
  i : Iso _ _
  i .fst = [ curry² inl , curry² inr ]ₓ
  i .snd .is-iso.inv = [ inxl $²_ , inxr $²_ ]ᵤ
  i .snd .is-iso.rinv (inl _) = refl
  i .snd .is-iso.rinv (inr _) = refl
  i .snd .is-iso.linv (inxl _ _) = refl
  i .snd .is-iso.linv (inxr _ _) = refl

⊻↪⊎ : (A ⊻ B) ↪ (A ⊎ B)
⊻↪⊎ = ≃→↪ ⊻≃×¬⊎×¬ ∙ ⊎↪ (fst , subset-proj-is-embedding (λ _ → hlevel 1)) (fst , subset-proj-is-embedding (λ _ → hlevel 1))
