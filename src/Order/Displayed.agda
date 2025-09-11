{-# OPTIONS --safe #-}
module Order.Displayed where

open import Cat.Prelude

open import Order.Base
open import Order.Morphism

record Displayed {ℓₒ ℓᵣ} ℓ ℓ' (P : Poset ℓₒ ℓᵣ) : Type (ℓsuc (ℓ ⊔ ℓ') ⊔ ℓₒ ⊔ ℓᵣ) where
  no-eta-equality

  private
    module P = Poset P

  field
    Ob[_]   : P.Ob → Type ℓ
    Rel[_]  : ∀ {x y} → x P.≤ y → Ob[ x ] → Ob[ y ] → Type ℓ'
    ≤-refl' : ∀ {x} {x' : Ob[ x ]} → Rel[ P.≤-refl ] x' x'
    ≤-thin' : ∀ {x y} (f : x P.≤ y) {x' y'} → is-prop (Rel[ f ] x' y')
    ≤-trans'
      : ∀ {x y z} {x' : Ob[ x ]} {y' : Ob[ y ]} {z' : Ob[ z ]}
      → {f : x P.≤ y} {g : y P.≤ z}
      → Rel[ f ] x' y' → Rel[ g ] y' z'
      → Rel[ P.≤-trans f g ] x' z'
    ≤-antisym'
      : ∀ {x} {x' y' : Ob[ x ]}
      → Rel[ P.≤-refl ] x' y' → Rel[ P.≤-refl ] y' x' → x' ＝ y'

  ≤-antisym-over
    : ∀ {x y} {f : x P.≤ y} {g : y P.≤ x} {x' y'}
    → Rel[ f ] x' y' → Rel[ g ] y' x'
    → Pathᴾ (λ i → Ob[ P.≤-antisym f g i ]) x' y'
  ≤-antisym-over {x} {f} {g} {x'} =
    transport
      (λ i → {f : x P.≤ p i} {g : p i P.≤ x} {y' : Ob[ p i ]}
           → Rel[ f ] x' y' → Rel[ g ] y' x'
           → Pathᴾ (λ j → Ob[ P.≤-antisym f g j ]) x' y')
      λ r s → transport
        (λ i → {f g : x P.≤ x} {y' : Ob[ x ]}
             → Rel[ P.≤-thin P.≤-refl f i ] x' y' → Rel[ P.≤-thin P.≤-refl g i ] y' x'
             → Pathᴾ (λ j → Ob[ P.ob-is-set _ _ refl (P.≤-antisym f g) i j ]) x' y')
        ≤-antisym' r s
    where p = P.≤-antisym f g

module _ {ℓ ℓ' ℓₒ ℓᵣ} {P : Poset ℓₒ ℓᵣ} (D : Displayed ℓ ℓ' P) where
  private
    module P = Poset P
    module D = Displayed D

  -- Total space of a displayed poset
  -- a preorder form of the Grothendieck construction

  ∫ : Poset (ℓ ⊔ ℓₒ) (ℓ' ⊔ ℓᵣ)
  ∫ .Poset.Ob = Σ ⌞ P ⌟ D.Ob[_]
  ∫ .Poset._≤_ (x , x') (y , y') = Σ (x P.≤ y) λ f → D.Rel[ f ] x' y'
  ∫ .Poset.≤-thin = Σ-is-of-hlevel 1 P.≤-thin λ f → D.≤-thin' f
  ∫ .Poset.≤-refl = P.≤-refl , D.≤-refl'
  ∫ .Poset.≤-trans (p , p') (q , q') = P.≤-trans p q , D.≤-trans' p' q'
  ∫ .Poset.≤-antisym (p , p') (q , q') =
    Σ-pathᴾ (P.≤-antisym p q) (D.≤-antisym-over p' q')

  -- Fibre poset

  Fibre : ⌞ P ⌟ → Poset ℓ ℓ'
  Fibre x .Poset.Ob = D.Ob[ x ]
  Fibre x .Poset._≤_ = D.Rel[ P.≤-refl ]
  Fibre x .Poset.≤-thin = D.≤-thin' P.≤-refl
  Fibre x .Poset.≤-refl = D.≤-refl'
  Fibre x .Poset.≤-trans p' q' =
    subst (λ p → D.Rel[ p ] _ _) (P.≤-thin _ _) $
    D.≤-trans' p' q'
  Fibre x .Poset.≤-antisym = D.≤-antisym'

  fibre-injᵖ : (x : ⌞ P ⌟) → Fibre x ⇒ ∫
  fibre-injᵖ x .hom    x'    = x , x'
  fibre-injᵖ x .pres-≤ x'≤y' = P.≤-refl , x'≤y'

  fibre-injᵖ-is-order-embedding
    : (x : ⌞ P ⌟) → is-order-embedding (Fibre x) ∫ (fibre-injᵖ x $_)
  fibre-injᵖ-is-order-embedding x =
    prop-extₑ (D.≤-thin' P.≤-refl) (∫ .Poset.≤-thin)
      (fibre-injᵖ x .pres-≤)
      (λ (p , p') → subst (λ p → D.Rel[ p ] _ _) (P.≤-thin p _) p')
