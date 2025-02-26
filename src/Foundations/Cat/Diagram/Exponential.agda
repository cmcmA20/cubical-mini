{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Exponential where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Diagram.Initial
open import Foundations.Cat.Diagram.Product.Binary
open import Foundations.Cat.Diagram.Terminal
open import Foundations.Cat.Reflexivity

private variable ℓa ℓb ℓe ℓg : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Refl Ob Hom ⦄
  ⦃ _ : Comp Ob Hom ⦄
  ⦃ _ : Binary-products Ob Hom ⦄
  where

  record is-exponential ℓg {A : Ob ℓa} {B : Ob ℓb}
    (B^A : Ob ℓe) (ev : Hom (B^A × A) B) : Type (ob-lvl ℓg l⊔ hom-lvl ℓg ℓe l⊔ hom-lvl (ℓg l⊔ ℓa) ℓb) where
    no-eta-equality
    field
      ƛ        : {Γ : Ob ℓg} → Hom (Γ × A) B → Hom Γ B^A
      commutes : {Γ : Ob ℓg} (m : Hom (Γ × A) B) → ev ∘ (ƛ m ×→ refl) ＝ m
      unique   : {Γ : Ob ℓg} {m : Hom (Γ × A) B} (m′ : Hom Γ B^A)
               → ev ∘ (m′ ×→ refl) ＝ m → m′ ＝ ƛ m

  record Exponential (A : Ob ℓa) (B : Ob ℓb) (B^A : Ob (ℓa l⊔ ℓb)) : Typeω where
    no-eta-equality
    field
      ev : Hom (B^A × A) B
      has-is-exp : is-exponential ℓg B^A ev

  record Cartesian-closed : Typeω where
    no-eta-equality
    infixr 50 _⇒_
    field
      _⇒_ : (A : Ob ℓa) (B : Ob ℓb) → Ob (ℓa l⊔ ℓb)
      has-exp : {A : Ob ℓa} {B : Ob ℓb} → Exponential A B (A ⇒ B)

open is-exponential ⦃ ... ⦄ public
  renaming (commutes to ƛ-commutes; unique to ƛ-unique)
open Exponential ⦃ ... ⦄ public
  using (ev)
open Cartesian-closed ⦃ ... ⦄ public
  using (_⇒_)

{-# DISPLAY is-exponential.ƛ _ f = ƛ f #-}
{-# DISPLAY is-exponential.commutes _ f = ƛ-commutes f #-}
{-# DISPLAY is-exponential.unique _ f p = ƛ-unique f p #-}
{-# DISPLAY Exponential.ev _ = ev #-}
{-# DISPLAY Cartesian-closed._⇒_ _ A B = A ⇒ B #-}

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Refl Ob Hom ⦄
  ⦃ _ : Comp Ob Hom ⦄
  ⦃ _ : Binary-products Ob Hom ⦄
  {A : Ob ℓa} {B : Ob ℓb}
  where instance
    is-exp-helper : {E : Ob (ℓa l⊔ ℓb)} ⦃ e : Exponential Ob Hom A B E ⦄ → is-exponential Ob Hom ℓg E ev
    is-exp-helper ⦃ e ⦄ = e .Exponential.has-is-exp

    exp-helper : ⦃ e : Cartesian-closed Ob Hom ⦄ → Exponential Ob Hom A B (A ⇒ B)
    exp-helper ⦃ e ⦄ = e .Cartesian-closed.has-exp

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄
  ⦃ _ : Binary-products Ob Hom ⦄ ⦃ _ : Cartesian-closed Ob Hom ⦄
  ⦃ _ : Initial Ob Hom {ℓg} ⦄
  where

  infixr 0 ¬_
  ¬_ : Ob ℓa → Ob (ℓa l⊔ ℓg)
  ¬ A = A ⇒ ⊥
