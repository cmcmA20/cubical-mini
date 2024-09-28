{-# OPTIONS --safe --no-exact-split #-}
module Order.Constructions.Coproduct where

open import Cat.Prelude
open import Cat.Diagram.Initial

open import Order.Base
import Order.Reasoning

open import Data.Sum

private variable o ℓ o′ ℓ′ o″ ℓ″ : Level

Initial-Poset : Initial (Posets o ℓ)
Initial-Poset .Initial.bot = ⊥
Initial-Poset .Initial.has-⊥ _ .fst .hom ()
Initial-Poset .Initial.has-⊥ _ .fst .pres-≤ ()
Initial-Poset .Initial.has-⊥ _ .snd _ = ext λ()

_⊎ₚ_ : Poset o ℓ → Poset o′ ℓ′ → Poset (o ⊔ o′) (ℓ ⊔ ℓ′)
_⊎ₚ_ {ℓ} {ℓ′} P Q = po module ⊎ₚ where
  module P = Order.Reasoning P
  module Q = Order.Reasoning Q

  po : Poset _ _
  po .Poset.Ob = ⌞ P ⌟ ⊎ ⌞ Q ⌟
  po .Poset._≤_ (inl p) (inl p′) = Lift ℓ′ (p P.≤ p′)
  po .Poset._≤_ (inr q) (inr q′) = Lift ℓ  (q Q.≤ q′)
  po .Poset._≤_ _ _ = ⊥
  po .Poset.≤-thin {inl p} {inl p′} = hlevel 1
  po .Poset.≤-thin {inr q} {inr q′} = hlevel 1
  po .Poset.≤-refl {inl p} = lift refl
  po .Poset.≤-refl {inr q} = lift refl
  po .Poset.≤-trans {inl p} {inl p′} {inl p″} (lift u) (lift v) = lift (u ∙ v)
  po .Poset.≤-trans {inr q} {inr q′} {inr q″} (lift u) (lift v) = lift (u ∙ v)
  po .Poset.≤-antisym {inl p} {inl p′} (lift u) (lift v) = inl # P.≤-antisym u v
  po .Poset.≤-antisym {inr q} {inr q′} (lift u) (lift v) = inr # Q.≤-antisym u v
{-# DISPLAY ⊎ₚ.po a b = a ⊎ₚ b #-}

instance
  ⊎-Poset : ⊎-notation (Poset o ℓ) (Poset o′ ℓ′) _
  ⊎-Poset .⊎-notation.Constraint _ _ = ⊤
  ⊎-Poset ._⊎_ P Q = P ⊎ₚ Q

module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  Inl : P ⇒ P ⊎ Q
  Inl .hom = inl
  Inl .pres-≤ = lift

  Inr : Q ⇒ P ⊎ Q
  Inr .hom = inr
  Inr .pres-≤ = lift

  [_,_]ₚ : {R : Poset o″ ℓ″} → P ⇒ R → Q ⇒ R → P ⊎ Q ⇒ R
  [ F , G ]ₚ .hom = [ F .hom , G .hom ]ᵤ
  [ F , G ]ₚ .pres-≤ {inl p} {inl p′} (lift u) = F # u
  [ F , G ]ₚ .pres-≤ {inr q} {inr q′} (lift v) = G # v
