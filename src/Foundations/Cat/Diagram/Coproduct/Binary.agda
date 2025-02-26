{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Coproduct.Binary where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition

private variable ℓa ℓb ℓs ℓq : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Comp Ob Hom ⦄
  where

  -- \(4 and \)4
  record is-coproduct ℓq {A : Ob ℓa} {B : Ob ℓb} {S : Ob ℓs} (ι₁ : Hom A S) (ι₂ : Hom B S) : Type (ob-lvl ℓq l⊔ hom-lvl ℓa ℓq l⊔ hom-lvl ℓb ℓq l⊔ hom-lvl ℓs ℓq) where
    no-eta-equality
    field
      ⁅_,_⁆ : {Q : Ob ℓq} (f : Hom A Q) (g : Hom B Q) → Hom S Q
      ⁅⁆∘ι₁ : {Q : Ob ℓq} {f : Hom A Q} {g : Hom B Q} → ⁅ f , g ⁆ ∘ ι₁ ＝ f
      ⁅⁆∘ι₂ : {Q : Ob ℓq} {f : Hom A Q} {g : Hom B Q} → ⁅ f , g ⁆ ∘ ι₂ ＝ g

      unique : {Q : Ob ℓq} {f : Hom A Q} {g : Hom B Q}
               {h : Hom S Q}
               (fs : h ∘ ι₁ ＝ f) (sn : h ∘ ι₂ ＝ g)
             → h ＝ ⁅ f , g ⁆

  record Coproduct (A : Ob ℓa) (B : Ob ℓb) (S : Ob (ℓa l⊔ ℓb)) : Typeω where
    no-eta-equality
    field
      ι₁  : Hom A S
      ι₂  : Hom B S
      has-is-coproduct : is-coproduct ℓq ι₁ ι₂

  -- \union 11
  record Binary-coproducts : Typeω where
    no-eta-equality
    infixr 70 _⨿_
    field
      _⨿_ : (A : Ob ℓa) (B : Ob ℓb) → Ob (ℓa l⊔ ℓb)
      has-coproduct : {A : Ob ℓa} {B : Ob ℓb} → Coproduct A B (A ⨿ B)


open is-coproduct ⦃ ... ⦄ public
  renaming (unique to ⁅⁆-unique)
open Coproduct ⦃ ... ⦄ public
  using (ι₁; ι₂)
open Binary-coproducts ⦃ ... ⦄ public
  using (_⨿_)

{-# DISPLAY is-coproduct.⁅_,_⁆ _ f g = ⁅ f , g ⁆ #-}
{-# DISPLAY is-coproduct.⁅⁆∘ι₁ _ = ⁅⁆∘ι₁ #-}
{-# DISPLAY is-coproduct.⁅⁆∘ι₂ _ = ⁅⁆∘ι₂ #-}
{-# DISPLAY is-coproduct.unique _ p q = ⁅⁆-unique p q #-}
{-# DISPLAY Coproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY Coproduct.ι₂ _ = ι₂ #-}
{-# DISPLAY Binary-coproducts._⨿_ _ A B = A ⨿ B #-}

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄
  {A : Ob ℓa} {B : Ob ℓb}
  where instance
    is-coproduct-helper : {S : Ob (ℓa l⊔ ℓb)} ⦃ c : Coproduct Ob Hom A B S ⦄ → is-coproduct Ob Hom ℓq ι₁ ι₂
    is-coproduct-helper ⦃ c ⦄ = c .Coproduct.has-is-coproduct

    coproduct-helper : ⦃ c : Binary-coproducts Ob Hom ⦄ → Coproduct Ob Hom A B (A ⨿ B)
    coproduct-helper ⦃ c ⦄ = c .Binary-coproducts.has-coproduct

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄
  ⦃ _ : Binary-coproducts Ob Hom ⦄
  where
  infixr 71 _⨿→_
  _⨿→_ : {A : Ob ℓa} {B : Ob ℓb} {P : Ob ℓs} {Q : Ob ℓq}
       → Hom P A → Hom Q B → Hom (P ⨿ Q) (A ⨿ B)
  f ⨿→ g = ⁅ f ∙ ι₁ , g ∙ ι₂ ⁆
