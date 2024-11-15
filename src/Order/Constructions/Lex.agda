{-# OPTIONS --safe --no-exact-split #-}
module Order.Constructions.Lex where

open import Cat.Prelude
open import Foundations.Base
open import Meta.Effect

open import Data.Sum.Base
open import Data.Sum.Path

open import Order.Base
open import Order.Strict

private variable o ℓ o′ ℓ′ o″ ℓ″ ℓᵢ ℓⱼ ℓₖ : Level

-- left strict + set, right poset
_<×≤_ : (P : StrictPoset o ℓ) → ⦃ _ : H-Level 2 (StrictPoset.Ob P) ⦄ → Poset o′ ℓ′ → Poset (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
P <×≤ Q = po module <×≤ where
  module P = StrictPoset P
  module Q = Poset Q

  po : Poset _ _
  po .Poset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  po .Poset._≤_ (px , qx) (py , qy) = (px P.< py) ⊎ ((px ＝ py) × (qx Q.≤ qy))
  po .Poset.≤-thin =
    disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
      λ where (px<py , px=py , _) → P.<→≠ px<py px=py
  po .Poset.≤-refl = inr (refl , Q.≤-refl)
  po .Poset.≤-trans                (inl px<py)           (inl py<pz)           =
    inl (P.<-trans px<py py<pz)
  po .Poset.≤-trans {x = (px , _)} (inl px<py)           (inr (py=pz , _))     =
    inl (subst (px P.<_) py=pz px<py)
  po .Poset.≤-trans {z = (pz , _)} (inr (px=py , _))     (inl py<pz)           =
    inl (subst (P._< pz) (px=py ⁻¹) py<pz)
  po .Poset.≤-trans                (inr (px=py , qx≤qy)) (inr (py=pz , qy≤qz)) =
    inr ( px=py ∙ py=pz , Q.≤-trans qx≤qy qy≤qz)
  po .Poset.≤-antisym (inl px<py)           (inl py<px)       =
    ⊥.rec (P.<-asym px<py py<px)
  po .Poset.≤-antisym (inl px<py)           (inr (py=px , _)) =
    ⊥.rec (P.<→≠ px<py (py=px ⁻¹))
  po .Poset.≤-antisym (inr (px=py , _))     (inl (py<px))     =
    ⊥.rec (P.<→≠ py<px (px=py ⁻¹))
  po .Poset.≤-antisym (inr (px=py , qx≤qy)) (inr (_ , qy≤qx)) =
    ×-path px=py (Q.≤-antisym qx≤qy qy≤qx)
{-# DISPLAY <×≤.po a b = a <×≤ b #-}

-- left set
_<×<_ : (P : StrictPoset o ℓ) → ⦃ _ : H-Level 2 (StrictPoset.Ob P) ⦄ → StrictPoset o′ ℓ′ → StrictPoset (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
P <×< Q = spo module <×< where
  module P = StrictPoset P
  module Q = StrictPoset Q

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  spo .StrictPoset._<_ (px , qx) (py , qy) = (px P.< py) ⊎ ((px ＝ py) × (qx Q.< qy))
  spo .StrictPoset.<-thin =
    disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
      λ where (px<py , px=py , _) → P.<→≠ px<py px=py
  spo .StrictPoset.<-irrefl (inl px<px)       = P.<-irrefl px<px
  spo .StrictPoset.<-irrefl (inr (_ , qx<qx)) = Q.<-irrefl qx<qx
  spo .StrictPoset.<-trans                (inl px<py)           (inl py<pz)           =
    inl (P.<-trans px<py py<pz)
  spo .StrictPoset.<-trans {x = (px , _)} (inl px<py)           (inr (py=pz , qy<qz)) =
    inl (subst (px P.<_) py=pz px<py)
  spo .StrictPoset.<-trans {z = (pz , _)} (inr (px=py , _))     (inl py<pz)           =
    inl (subst (P._< pz) (px=py ⁻¹) py<pz)
  spo .StrictPoset.<-trans                (inr (px=py , qx<qy)) (inr (py=pz , qy<qz)) =
    inr ( px=py ∙ py=pz , Q.<-trans qx<qy qy<qz)
{-# DISPLAY <×<.spo a b = a <×< b #-}

-- truncated
_<×<₁_ : StrictPoset o ℓ → StrictPoset o′ ℓ′ → StrictPoset (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
P <×<₁ Q = spo module <×<₁ where
  module P = StrictPoset P
  module Q = StrictPoset Q

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  spo .StrictPoset._<_ (px , qx) (py , qy) = (px P.< py) ⊎ (∥ px ＝ py ∥₁ × (qx Q.< qy))
  spo .StrictPoset.<-thin =
    disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
      λ where (px<py , px=py₁ , _) → rec! (P.<→≠ px<py) px=py₁
  spo .StrictPoset.<-irrefl (inl px<px)       = P.<-irrefl px<px
  spo .StrictPoset.<-irrefl (inr (_ , qx<qx)) = Q.<-irrefl qx<qx
  spo .StrictPoset.<-trans                (inl px<py)            (inl py<pz)            =
    inl (P.<-trans px<py py<pz)
  spo .StrictPoset.<-trans {x = (px , _)} (inl px<py)            (inr (py=pz₁ , _))     =
    inl (rec! (λ e → subst (px P.<_) e px<py) py=pz₁)
  spo .StrictPoset.<-trans {z = (pz , _)} (inr (px=py₁ , _))     (inl py<pz)            =
    inl (rec! (λ e → subst (P._< pz) (e ⁻¹) py<pz) px=py₁)
  spo .StrictPoset.<-trans                (inr (px=py₁ , qx<qy)) (inr (py=pz₁ , qy<qz)) =
    inr ((do px=py ← px=py₁
             py=pz ← py=pz₁
             pure (px=py ∙ py=pz))
         , Q.<-trans qx<qy qy<qz)
{-# DISPLAY <×<₁.spo a b = a <×<₁ b #-}
