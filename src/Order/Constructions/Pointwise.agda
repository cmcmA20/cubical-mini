{-# OPTIONS --safe #-}
module Order.Constructions.Pointwise where

open import Categories.Prelude
open import Order.Base
open import Order.Constructions.Product
open import Order.Constructions.Props
import Order.Reasoning

private variable o ℓ o′ ℓ′ ℓᵢ : Level

Pointwise : (I : Type ℓᵢ) (P : I → Poset o ℓ) → Poset (ℓᵢ ⊔ o) (ℓᵢ ⊔ ℓ)
Pointwise I P = po where
  open module P {i} = Order.Reasoning (P i)
  po : Poset _ _
  po .Poset.Ob = Π[ P ]
  po .Poset._≤_ f g = ∀[ i ꞉ I ] (f i ⇒ g i)
  po .Poset.≤-thin = hlevel 1
  po .Poset.≤-refl = refl
  po .Poset.≤-trans f≤g g≤h = f≤g ∙ g≤h
  po .Poset.≤-antisym f≤g g≤h = ext (λ _ → ≤-antisym f≤g g≤h)

tupleₚ
  : {I : Type ℓᵢ} {P : I → Poset o ℓ} {R : Poset o′ ℓ′}
  → (∀ i → R ⇒ P i)
  → R ⇒ Pointwise I P
tupleₚ f .hom x i = f i # x
tupleₚ f .pres-≤ x≤y = f _ .pres-≤ x≤y

projₚ
  : {I : Type ℓᵢ} {P : I → Poset o ℓ} (i : I)
  → Pointwise I P ⇒ P i
projₚ i .hom f      = f i
projₚ i .pres-≤ f≤g = f≤g

Poset[_,_]
  : (P : Poset o ℓ) (Q : Poset o′ ℓ′)
  → Poset (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (o ⊔ ℓ′)
Poset[_,_] P Q = po module Poset[_,_] where
  open Order.Reasoning Q
  po : Poset _ _
  po .Poset.Ob       = P ⇒ Q
  po .Poset._≤_ f g  = Π[ x ꞉ P ] f # x ≤ g # x
  po .Poset.≤-thin   = hlevel 1
  po .Poset.≤-refl _ = refl
  po .Poset.≤-trans   f≤g g≤h x = f≤g x ∙ g≤h x
  po .Poset.≤-antisym f≤g g≤f   = ext λ x → ≤-antisym (f≤g x) (g≤f x)
{-# DISPLAY Poset[_,_].po a b = Poset[ a , b ] #-}

instance
  ⇒-Poset-exp : ⇒-notation (Poset o ℓ) (Poset o′ ℓ′) (Poset (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (o ⊔ ℓ′))
  ⇒-Poset-exp ._⇒_ = Poset[_,_]
