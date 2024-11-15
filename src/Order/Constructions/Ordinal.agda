{-# OPTIONS --safe #-}
module Order.Constructions.Ordinal where

open import Cat.Prelude
open import Foundations.HLevel.Closure

open import Order.Base
open import Data.Unit.Base
open import Data.Acc.Base
open import Data.Acc.Properties
open import Data.Sum.Base
open import Data.Sum.Path
open import Order.Ordinal
open import Order.Constructions.Lex

private variable
  ℓ : Level

suco : Ordinal ℓ → Ordinal ℓ
suco {ℓ} (W , tr) = Wsuc , λ {x} {y} {z} → ws-trans {x} {y} {z}
  where
  module W = WESet W
  _<ws_ : ⊤ ⊎ W.Ob → ⊤ ⊎ W.Ob → 𝒰 ℓ
  (inl _) <ws  _      = ⊥
  (inr _) <ws (inl _) = ⊤
  (inr x) <ws (inr y) = x W.< y

  ws-trans : ∀ {x y z} → x <ws y → y <ws z → x <ws z
  ws-trans {x = inr x} {y = inr y} {z = inl tt} _  _  = lift tt
  ws-trans {x = inr x} {y = inr y} {z = inr z}  xy yz = tr xy yz

  ws-wf : is-wf _<ws_
  ws-wf (inl tt) = acc λ where
                           (inl tt) ()
                           (inr x) _ → ws-wf (inr x)
  ws-wf (inr x) = to-induction W.<-wf (Acc _<ws_ ∘ₜ inr)
                    (λ z ih → acc λ where
                                      (inl tt) ()
                                      (inr q) → ih q)
                    x

  Wsuc : WESet ℓ ℓ
  Wsuc .WESet.Ob = ⊤ ⊎ W.Ob
  Wsuc .WESet._<_ = _<ws_
  Wsuc .WESet.<-thin {x = inr x} {y = inl _} = hlevel!
  Wsuc .WESet.<-thin {x = inr x} {y = inr y} = hlevel!
  Wsuc .WESet.<-wf = ws-wf
  Wsuc .WESet.<-lext {x = inl tt} {y = inl tt} eqv = refl
  Wsuc .WESet.<-lext {x = inl tt} {y = inr y}  eqv =
    ⊥.rec (wf→irrefl W.<-wf y (eqv (inr y) $ lift tt))
  Wsuc .WESet.<-lext {x = inr x}  {y = inl tt} eqv =
    ⊥.rec (wf→irrefl W.<-wf x (eqv (inr x) ⁻¹ $ lift tt))
  Wsuc .WESet.<-lext {x = inr x}  {y = inr y}  eqv =
    ap inr $
    W.<-lext λ z →
    prop-extₑ! (eqv (inr z) $_) (eqv (inr z) ⁻¹ $_)

_+o_ : Ordinal ℓ → Ordinal ℓ → Ordinal ℓ
_+o_ {ℓ} (W₁ , tr₁) (W₂ , tr₂) = W+ , λ {x} {y} {z} → w+-trans {x} {y} {z}
  where
  module W₁ = WESet W₁
  module W₂ = WESet W₂

  _<w+_ : W₁.Ob ⊎ W₂.Ob → W₁.Ob ⊎ W₂.Ob → 𝒰 ℓ
  (inl x₁) <w+ (inl y₁) = x₁ W₁.< y₁
  (inl x₁) <w+ (inr y₁) = ⊤
  (inr x₂) <w+ (inl y₁) = ⊥
  (inr x₂) <w+ (inr y₂) = x₂ W₂.< y₂

  w+-trans : ∀ {x y z} → x <w+ y → y <w+ z → x <w+ z
  w+-trans {x = inl x₁} {y = inl y₁} {z = inl z₁} xy yz = tr₁ xy yz
  w+-trans {x = inl x₁} {y = inl y₁} {z = inr z₂} xy yz = lift tt
  w+-trans {x = inl x₁} {y = inr y₂} {z = inr z₂} xy yz = lift tt
  w+-trans {x = inr x₂} {y = inr y₂} {z = inr z₂} xy yz = tr₂ xy yz

  w+-wf : is-wf _<w+_
  w+-wf (inl x₁) =
    to-induction W₁.<-wf (Acc _<w+_ ∘ₜ inl)
      (λ z₁ ih → acc λ where
                        (inl y₁) → ih y₁
                        (inr y₂) ())
      x₁
  w+-wf (inr x₂) =
    to-induction W₂.<-wf (Acc _<w+_ ∘ₜ inr)
      (λ z₂ ih → acc λ where
                        (inl y₁) _ → w+-wf (inl y₁)
                        (inr y₂) → ih y₂)
      x₂

  W+ : WESet ℓ ℓ
  W+ .WESet.Ob = W₁.Ob ⊎ W₂.Ob
  W+ .WESet._<_ = _<w+_
  W+ .WESet.<-thin {x = inl x₁} {y = inl y₁} = W₁.<-thin
  W+ .WESet.<-thin {x = inl x₁} {y = inr y₂} = hlevel!
  W+ .WESet.<-thin {x = inr x₂} {y = inl y₁} = hlevel!
  W+ .WESet.<-thin {x = inr x₂} {y = inr y₂} = W₂.<-thin
  W+ .WESet.<-wf = w+-wf
  W+ .WESet.<-lext {x = inl x₁} {y = inl y₁} eqv =
    ap inl $
    W₁.<-lext λ z →
    prop-extₑ! (eqv (inl z) $_) (eqv (inl z) ⁻¹ $_)
  W+ .WESet.<-lext {x = inl x₁} {y = inr y₂} eqv =
   ⊥.rec (wf→irrefl W₁.<-wf x₁ (eqv (inl x₁) ⁻¹ $ lift tt))
  W+ .WESet.<-lext {x = inr x₂} {y = inl y₁} eqv =
   ⊥.rec (wf→irrefl W₁.<-wf y₁ (eqv (inl y₁) $ lift tt))
  W+ .WESet.<-lext {x = inr x₂} {y = inr y₂} eqv =
    ap inr $
    W₂.<-lext λ z →
    prop-extₑ! (eqv (inr z) $_) (eqv (inr z) ⁻¹ $_)

_∙o_ : Ordinal ℓ → Ordinal ℓ → Ordinal ℓ
_∙o_ {ℓ} (W₁ , tr₁) (W₂ , tr₂) = W∙ , λ {x} {y} {z} → w∙-trans {x} {y} {z}
  where
  module W₁ = WESet W₁
  module W₂ = WESet W₂

  -- reverse lex
  _<w∙_ : W₁.Ob × W₂.Ob → W₁.Ob × W₂.Ob → 𝒰 ℓ
  _<w∙_ (x₁ , x₂) (y₁ , y₂) = ×-lex W₂._<_ W₁._<_ (x₂ , x₁) (y₂ , y₁)

  w∙-trans : ∀ {x y z} → x <w∙ y → y <w∙ z → x <w∙ z
  w∙-trans {x = (x₁ , x₂)} {y = (y₁ , y₂)} = ×-lex-trans tr₂ tr₁ {pqx = (x₂ , x₁)} {pqy = (y₂ , y₁)}

  w∙-wf : is-wf _<w∙_
  w∙-wf (x₁ , x₂) =
    to-induction W₂.<-wf (λ y₂ → ∀ y₁ → Acc _<w∙_ (y₁ , y₂))
      (λ y₂ ih₂ →
        to-induction W₁.<-wf (λ z₁ → Acc _<w∙_ (z₁ , y₂))
          λ y₁ ih₁ →
            acc λ where
                   (a₁ , a₂) (inl a<y₂)          → ih₂ a₂ a<y₂ a₁
                   (a₁ , a₂) (inr (a=y₂ , a<y₁)) → subst (λ q → Acc _<w∙_ (a₁ , q)) (a=y₂ ⁻¹) $ ih₁ a₁ a<y₁)
      x₂ x₁

  W∙ : WESet ℓ ℓ
  W∙ .WESet.Ob = W₁.Ob × W₂.Ob
  W∙ .WESet._<_ = _<w∙_
  W∙ .WESet.<-thin {x = (_ , x₂)} {y = (_ , y₂)} =
    disjoint-⊎-is-prop (hlevel 1) (×-is-of-hlevel 1 (W₂.ob-is-set x₂ y₂) hlevel!)
       λ where (x<y₂ , x=y₂ , _) → wf→irrefl W₂.<-wf x₂ (subst (x₂ W₂.<_) (x=y₂ ⁻¹) x<y₂)
  W∙ .WESet.<-wf = w∙-wf
  W∙ .WESet.<-lext {x = x₁ , x₂} {y = y₁ , y₂} eqv =
    let x=y₂ = W₂.<-lext λ z →
                 prop-extₑ!
                   (λ z<x₂ → [ refl
                             , (λ where (_ , y<y₁) → ⊥.rec (wf→irrefl W₁.<-wf y₁ y<y₁))
                             ]ᵤ (eqv (y₁ , z) $ inl z<x₂))
                   λ z<y₂ → [ refl
                             , (λ where (_ , x<x₁) → ⊥.rec (wf→irrefl W₁.<-wf x₁ x<x₁))
                             ]ᵤ (eqv (x₁ , z) ⁻¹ $ (inl z<y₂))
      in
    ×-path
      (W₁.<-lext λ z →
        prop-extₑ!
          (λ z<x₁ → [ (λ x<y₂ → ⊥.rec (wf→irrefl W₂.<-wf x₂ (subst (x₂ W₂.<_) (x=y₂ ⁻¹) x<y₂)))
                    , snd
                    ]ᵤ (eqv (z , x₂) $ inr (refl , z<x₁)))
          λ z<y₁ → [ (λ y<x₂ → ⊥.rec (wf→irrefl W₂.<-wf y₂ (subst (y₂ W₂.<_) x=y₂ y<x₂)))
                    , snd
                    ]ᵤ (eqv (z , y₂) ⁻¹ $ inr (refl , z<y₁)))
      x=y₂
