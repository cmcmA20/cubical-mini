{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Product.Indexed where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Underlying

private variable ℓi ℓp ℓf ℓg ℓy : Level

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Comp Ob Hom ⦄ {Idx : Type ℓi}
  where

  record is-indexed-product ℓy {P : Ob ℓp} (F : Idx → Ob ℓf) (π : ∀ i → Hom P (F i)) : Type (ℓi l⊔ ob-lvl ℓy l⊔ hom-lvl ℓy ℓp l⊔ hom-lvl ℓy ℓf) where
    no-eta-equality
    field
      tuple   : {Y : Ob ℓy} → (∀ i → Hom Y (F i)) → Hom Y P
      commute : ∀{i} {Y : Ob ℓy} {f : ∀ i → Hom Y (F i)} → π i ∘ tuple f ＝ f i
      unique  : {Y : Ob ℓy} {h : Hom Y P} (f : ∀ i → Hom Y (F i)) → (∀ i → π i ∘ h ＝ f i) → h ＝ tuple f

  record Indexed-product (F : Idx → Ob ℓf) (∏F : Ob (ℓi l⊔ ℓf)) : Typeω where
    no-eta-equality
    field
      π         : ∀ i → Hom ∏F (F i)
      has-is-ip : is-indexed-product ℓy F π

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  ⦃ _ : Comp Ob Hom ⦄ (Idx : Type ℓi)
  where
  -- take care, it's not a greek letter pi, it's n-ary product symbol (\prod)
  record Indexed-products : Typeω where
    no-eta-equality
    infixr 60 ∏
    field
      ∏      : (Idx → Ob ℓf) → Ob (ℓi l⊔ ℓf)
      has-ip : {F : Idx → Ob ℓf} → Indexed-product Ob Hom F (∏ F)

open is-indexed-product ⦃ ... ⦄ public
  renaming (tuple to ∏-tuple; commute to π-commute; unique to ∏-unique)
open Indexed-product ⦃ ... ⦄ public
  using (π)
open Indexed-products ⦃ ... ⦄ public
  using (∏)

{-# DISPLAY is-indexed-product.tuple _ F = ∏-tuple F #-}
{-# DISPLAY is-indexed-product.commute _ = π-commute #-}
{-# DISPLAY is-indexed-product.unique _ p q = ∏-unique p q #-}
{-# DISPLAY Indexed-product.π _ i = π i #-}
{-# DISPLAY Indexed-products.∏ _ F = ∏ F #-}

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄
  where

  ∏[_] : {Idx : Type ℓi} ⦃ _ : Indexed-products Ob Hom Idx ⦄ → (Idx → Ob ℓf) → Ob (ℓi l⊔ ℓf)
  ∏[_] = ∏

  -- and this one is \Pi
  Π-syntax : ⦃ u : Underlying Ob Hom ⦄ (X : Ob ℓi) ⦃ _ : Indexed-products Ob Hom ⌞ X ⌟ ⦄
           → (⌞ X ⌟ → Ob ℓf) → Ob (ℓf l⊔ u .ℓ-und ℓi)
  Π-syntax _ F = ∏ F
  syntax Π-syntax X (λ x → F) = Π[ x ꞉ X ] F

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ {Idx : Type ℓi} {F : Idx → Ob ℓf}
  where instance
    is-ip-helper : {ΠF : Ob (ℓi l⊔ ℓf)} ⦃ ip : Indexed-product Ob Hom F ΠF ⦄ → is-indexed-product Ob Hom ℓy F π
    is-ip-helper ⦃ ip ⦄ = ip .Indexed-product.has-is-ip

    ip-helper : ⦃ ip : Indexed-products Ob Hom Idx ⦄ → Indexed-product Ob Hom F ∏[ F ]
    ip-helper ⦃ ip ⦄ = ip .Indexed-products.has-ip

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Comp Ob Hom ⦄ {Idx : Type ℓi} {F : Idx → Ob ℓf} {G : Idx → Ob ℓg}
  ⦃ _ : Indexed-products Ob Hom Idx ⦄
  where
    ∏→ : (α : (i : Idx) → Hom (F i) (G i)) → Hom ∏[ F ] ∏[ G ]
    ∏→ α = ∏-tuple λ i → π i ∙ α i
