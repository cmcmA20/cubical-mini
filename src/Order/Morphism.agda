{-# OPTIONS --safe #-}
module Order.Morphism where

open import Categories.Prelude
import Categories.Morphism
open import Order.Base
import Order.Reasoning

private variable
  o o′ ℓ ℓ′ : Level
  P Q : Poset o ℓ

module _ (P : Poset o ℓ) (Q : Poset o′ ℓ′) (f : ⌞ P ⌟ → ⌞ Q ⌟) where
  private
    module P = Poset P
    module Q = Poset Q

  is-antitone : Type _
  is-antitone = ∀ {x y} → x ⇒ y → f y ⇒ f x

  is-order-reflection : Type _
  is-order-reflection = ∀ {x y} → f x ⇒ f y → x ⇒ y

  is-order-embedding : Type _
  is-order-embedding = ∀ {x y} → (x ⇒ y) ≃ (f x ⇒ f y)

  is-order-embedding→is-embedding : is-order-embedding → is-embedding f
  is-order-embedding→is-embedding e = set-injective→is-embedding! λ fx=fy →
    let
      x≤y = e ⁻¹ $ =→~ fx=fy
      y≤x = e ⁻¹ $ =→~ $ sym fx=fy
    in P.≤-antisym x≤y y≤x

  monotone-reflection→is-order-embedding
    : is-monotone P Q f → is-order-reflection → is-order-embedding
  monotone-reflection→is-order-embedding p _ .fst = p
  monotone-reflection→is-order-embedding p q .snd = biimp-is-equiv! p q


module _ {o ℓ o′ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q

  open Order.Reasoning P

  section→order-reflection
    : (f : ⌞ P ⌟ → ⌞ Q ⌟) (g : Q ⇒ P)
    → f is-right-inverse-of (g #_)
    → is-order-reflection P Q f
  section→order-reflection f g sect {x = x} {y = y} fx≤fy =
    x         =⟨ sect x ⟨
    g # f x   ≤⟨ g .pres-≤ fx≤fy ⟩
    g # f y   =⟨ sect y ⟩
    y         ∎

  section→order-embedding
    : (f : P ⇒ Q) (g : Q ⇒ P)
    → f #_ is-right-inverse-of g #_
    → is-order-embedding P Q (f #_)
  section→order-embedding f g sect =
    monotone-reflection→is-order-embedding P Q _
      (f .pres-≤) (section→order-reflection (f #_) g sect)

module _ {o ℓ} {P Q : Poset o ℓ} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q

  open Categories.Morphism (Posets o ℓ)

  has-retract→is-order-reflection
    : (f : P ⇒ Q)
    → has-retract f
    → is-order-reflection P Q (f #_)
  has-retract→is-order-reflection f f-ret =
    section→order-reflection (f #_) (f-ret .retract) (f-ret .is-retract $ₚ_)

  has-retract→is-order-embedding
    : (f : P ⇒ Q)
    → has-retract f
    → is-order-embedding P Q (f #_)
  has-retract→is-order-embedding f f-ret =
    section→order-embedding f (f-ret .retract) (f-ret .is-retract $ₚ_)

  order-iso-is-order-embedding
    : (f : P ≅ Q) → is-order-embedding P Q (f .to #_)
  order-iso-is-order-embedding f =
    has-retract→is-order-embedding (f .to) (iso→to-has-retract f)
