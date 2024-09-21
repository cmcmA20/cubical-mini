{-# OPTIONS --safe #-}
module Cat.Constructions.Discrete where

open import Cat.Prelude

private variable
  ℓ ℓ′ o h : Level
  A : Type ℓ
  C : Precategory o h

open Precategory
open Functor
open _=>_

Disc : is-groupoid A → Precategory _ _
Disc {A} _ .Ob = A
Disc _ .Hom = _＝_
Disc A-is-grp .Hom-set = path-is-of-hlevel 2 A-is-grp
Disc _ .id = refl
Disc _ ._∘_ f g = g ∙ f
Disc _ .id-r = ∙-id-o
Disc _ .id-l = ∙-id-i
Disc _ .assoc = ∙-assoc

Disc! : (A : Type ℓ) ⦃ A-is-grp : H-Level 3 A ⦄
      → Precategory ℓ ℓ
Disc! A ⦃ A-is-grp ⦄ = Disc {A = A} hlevel!

Disc₃ : Grpd ℓ → Precategory ℓ ℓ
Disc₃ A = Disc! ⌞ A ⌟

Disc₂ : Set ℓ → Precategory ℓ ℓ
Disc₂ A = Disc! ⌞ A ⌟


lift-disc₂
  : {A : Set ℓ} {B : Set ℓ′}
  → ⌞ A ⇒ B ⌟
  → Functor (Disc₂ A) (Disc₂ B)
lift-disc₂ f .F₀   = f
lift-disc₂ f .F₁   = ap f
lift-disc₂ _ .F-id = refl
lift-disc₂ f .F-∘  = flip (ap-comp-∙ f)

Codisc : Type ℓ → Precategory ℓ ℓ′
Codisc A .Ob = A
Codisc _ .Hom _ _ = ⊤
Codisc _ .Hom-set = hlevel!
Codisc _ .id = _
Codisc _ ._∘_ _ _ = _
Codisc _ .id-l _ = refl
Codisc _ .id-r _ = refl
Codisc _ .assoc _ _ _ = refl

-- TODO diagrams
