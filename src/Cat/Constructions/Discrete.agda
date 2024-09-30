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

Disc : (A : Type ℓ) → Precategory _ _
Disc A .Ob = A
Disc _ .Hom = _＝_
Disc _ .id = refl
Disc _ ._∘_ f g = g ∙ f
Disc _ .id-r = ∙-id-o
Disc _ .id-l = ∙-id-i
Disc _ .assoc = ∙-assoc

lift-disc
  : {A : Type ℓ} {B : Type ℓ′}
  → (A → B)
  → Functor (Disc A) (Disc B)
lift-disc f .F₀   = f
lift-disc f .F₁   = ap f
lift-disc _ .F-id = refl
lift-disc f .F-∘  = flip (ap-comp-∙ f)

Codisc : Type ℓ → Precategory ℓ ℓ′
Codisc A .Ob = A
Codisc _ .Hom _ _ = ⊤
Codisc _ .id = _
Codisc _ ._∘_ _ _ = _
Codisc _ .id-l _ = refl
Codisc _ .id-r _ = refl
Codisc _ .assoc _ _ _ = refl

-- -- TODO diagrams
