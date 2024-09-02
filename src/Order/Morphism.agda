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


module _ {o ℓ o′ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q

  open Order.Reasoning P

  is-order-embedding→is-embedding : (f : ⌞ P ⌟ → ⌞ Q ⌟) → is-order-embedding P Q f → is-embedding f
  is-order-embedding→is-embedding f e = set-injective→is-embedding! λ fx=fy →
    let
      x≤y = e ⁻¹ $ =→~ $ fx=fy
      y≤x = e ⁻¹ $ =→~ $ fx=fy ⁻¹
    in P.≤-antisym x≤y y≤x

  monotone-reflection→is-order-embedding
    : (f : ⌞ P ⌟ → ⌞ Q ⌟) → is-monotone P Q f → is-order-reflection P Q f → is-order-embedding P Q f
  monotone-reflection→is-order-embedding f p _ .fst = p
  monotone-reflection→is-order-embedding f p q .snd = biimp-is-equiv! p q

  section→is-order-reflection
    : (f : ⌞ P ⌟ → ⌞ Q ⌟) (g : Q ⇒ P)
    → f section-of (g #_)
    → is-order-reflection P Q f
  section→is-order-reflection f g sect {x = x} {y = y} fx≤fy =
    x         =⟨ sect # x ⟨
    g # f x   ≤⟨ g # fx≤fy ⟩
    g # f y   =⟨ sect # y ⟩
    y         ∎

  section→is-order-embedding
    : (f : P ⇒ Q) (g : Q ⇒ P)
    → (f #_) section-of (g #_)
    → is-order-embedding P Q (f #_)
  section→is-order-embedding f g sect =
    monotone-reflection→is-order-embedding (f #_) (f #_)
      (section→is-order-reflection (f #_) g sect)


module _ {o o′ ℓ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q

  has-retract→is-order-reflection
    : (f : P ⇒ Q)
    → has-retract f
    → is-order-reflection P Q (f #_)
  has-retract→is-order-reflection f f-ret =
    section→is-order-reflection (f .hom) (f-ret .retract)
      (fun-ext $ ap hom (f-ret .is-retract) #_)

  has-retract→is-order-embedding
    : (f : P ⇒ Q)
    → has-retract f
    → is-order-embedding P Q (f #_)
  has-retract→is-order-embedding f f-ret =
    section→is-order-embedding f (f-ret .retract)
      (fun-ext $ ap hom (f-ret .is-retract) #_)

  ≅→is-order-embedding
    : (f : P ≅ Q) → is-order-embedding P Q (f #_)
  ≅→is-order-embedding f =
    has-retract→is-order-embedding (f .to) (≅→to-has-retract f)
    where open Iso
