{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Coproduct.Indexed where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Underlying

private variable ℓi ℓs ℓf ℓg ℓy : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Comp Ob Hom ⦄ {Idx : Type ℓi}
  where

  record is-indexed-coproduct ℓy {S : Ob ℓs} (F : Idx → Ob ℓf) (ι : ∀ i → Hom (F i) S) : Type (ℓi l⊔ ob-lvl ℓy l⊔ hom-lvl ℓs ℓy l⊔ hom-lvl ℓf ℓy) where
    no-eta-equality
    field
      match   : {Y : Ob ℓy} → (∀ i → Hom (F i) Y) → Hom S Y
      commute : ∀{i} {Y : Ob ℓy} {f : ∀ i → Hom (F i) Y} → match f ∘ ι i ＝ f i
      unique  : {Y : Ob ℓy} {h : Hom S Y} (f : ∀ i → Hom (F i) Y) → (∀ i → h ∘ ι i ＝ f i) → h ＝ match f

  record Indexed-coproduct (F : Idx → Ob ℓf) (∐F : Ob (ℓi l⊔ ℓf)) : Typeω where
    no-eta-equality
    field
      ι         : ∀ i → Hom (F i) ∐F
      has-is-ic : is-indexed-coproduct ℓy F ι

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Comp Ob Hom ⦄ (Idx : Type ℓi)
  where

  record Indexed-coproducts : Typeω where
    no-eta-equality
    field
      ∐      : (Idx → Ob ℓf) → Ob (ℓi l⊔ ℓf)
      has-ic : {F : Idx → Ob ℓf} → Indexed-coproduct Ob Hom F (∐ F)

open is-indexed-coproduct ⦃ ... ⦄ public
  renaming (match to ∐-match; commute to ι-commute; unique to ∐-unique)
open Indexed-coproduct ⦃ ... ⦄ public
  using (ι)
open Indexed-coproducts ⦃ ... ⦄ public
  using (∐)

{-# DISPLAY is-indexed-coproduct.match _ F = ∐-match F #-}
{-# DISPLAY is-indexed-coproduct.commute _ = ι-commute #-}
{-# DISPLAY is-indexed-coproduct.unique _ p q = ∐-unique p q #-}
{-# DISPLAY Indexed-coproduct.ι _ i = ι i #-}
{-# DISPLAY Indexed-coproducts.∐ _ F = ∐ F #-}

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄
  where

  ∐[_] : {Idx : Type ℓi} ⦃ _ : Indexed-coproducts Ob Hom Idx ⦄ → (Idx → Ob ℓf) → Ob (ℓi l⊔ ℓf)
  ∐[_] = ∐

  Σ-syntax : ⦃ u : Underlying Ob Hom ⦄ (X : Ob ℓi) ⦃ _ : Indexed-coproducts Ob Hom ⌞ X ⌟ ⦄
           → (⌞ X ⌟ → Ob ℓf) → Ob (ℓf l⊔ u .ℓ-und ℓi)
  Σ-syntax _ F = ∐ F
  syntax Σ-syntax X (λ x → F) = Σ[ x ꞉ X ] F

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ {Idx : Type ℓi} {F : Idx → Ob ℓf}
  where instance
    is-ic-helper : {∐F : Ob (ℓi l⊔ ℓf)} ⦃ ic : Indexed-coproduct Ob Hom F ∐F ⦄ → is-indexed-coproduct Ob Hom ℓy F ι
    is-ic-helper ⦃ ic ⦄ = ic .Indexed-coproduct.has-is-ic

    ic-helper : ⦃ ic : Indexed-coproducts Ob Hom Idx ⦄ → Indexed-coproduct Ob Hom F ∐[ F ]
    ic-helper ⦃ ic ⦄ = ic .Indexed-coproducts.has-ic

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ {Idx : Type ℓi} {F : Idx → Ob ℓf} {G : Idx → Ob ℓg}
  ⦃ _ : Indexed-coproducts Ob Hom Idx ⦄
  where
    ∐→ : (α : (i : Idx) → Hom (F i) (G i)) → Hom ∐[ F ] ∐[ G ]
    ∐→ α = ∐-match λ i → α i ∙ ι i
