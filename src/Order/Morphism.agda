{-# OPTIONS --safe #-}
module Order.Morphism where

open import Cat.Prelude
import Cat.Morphism
open import Order.Base
open import Functions.Surjection

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
    module P = Poset P
    module Q = Poset Q

  open Poset P

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
  section→is-order-reflection f g sect {x} {y} fx≤fy =
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
    module P = Poset P
    module Q = Poset Q
  open Iso

  has-retraction→is-order-reflection
    : (f : P ⇒ Q)
    → has-retraction f
    → is-order-reflection P Q (f #_)
  has-retraction→is-order-reflection f f-ret =
    section→is-order-reflection (f .hom) (f-ret .retraction)
      (fun-ext $ ap hom (f-ret .is-retraction) #_)

  has-retraction→is-order-embedding
    : (f : P ⇒ Q)
    → has-retraction f
    → is-order-embedding P Q (f #_)
  has-retraction→is-order-embedding f f-ret =
    section→is-order-embedding f (f-ret .retraction)
      (fun-ext $ ap hom (f-ret .is-retraction) #_)

  reflection-retraction→is-monotone
    : (f : ⌞ P ⌟ → ⌞ Q ⌟) (g : ⌞ Q ⌟ → ⌞ P ⌟)
    → f retraction-of g
    → is-order-reflection P Q f
    → is-monotone Q P g
  reflection-retraction→is-monotone f g r or {x} {y} le =
    or $ =→~⁻ (r ⁻¹ $ x) ∙ le ∙ =→~ (r ⁻¹ $ y)

  ≅ₚ→⊣ : (f : P ≅ Q) → f .to ⊣ f .from
  ≅ₚ→⊣ f .Adjoint.η ._=>ₚ_.η x = =→~⁻ λ i → f .inv-i i .hom x
  ≅ₚ→⊣ f .Adjoint.ε ._=>ₚ_.η y = =→~ λ i → f .inv-o i .hom y
  ≅ₚ→⊣ f .Adjoint.zig _ = prop!
  ≅ₚ→⊣ f .Adjoint.zag _ = prop!

  ≅→is-order-embedding
    : (f : P ≅ Q) → is-order-embedding P Q (f #_)
  ≅→is-order-embedding f =
    has-retraction→is-order-embedding (f .to) (≅→to-has-retraction f)

  iso-order-embedding→≅
    : (f : ⌞ P ⌟ ≅ ⌞ Q ⌟)
    → is-order-embedding P Q (f #_)
    → P ≅ Q
  iso-order-embedding→≅ f oe .to .hom = f #_
  iso-order-embedding→≅ f oe .to .pres-≤ = oe #_
  iso-order-embedding→≅ f oe .from .hom = f ⁻¹ $_
  iso-order-embedding→≅ f oe .from .pres-≤ =
    reflection-retraction→is-monotone (f #_) (f ⁻¹ $_)
     (f .inv-o) (oe ⁻¹ $_)
  iso-order-embedding→≅ f oe .inverses .Inverses.inv-o =
    ext $ f .inv-o #_
  iso-order-embedding→≅ f oe .inverses .Inverses.inv-i =
    ext $ f .inv-i #_

  iso-mono-refl→≅
    : (f : ⌞ P ⌟ ≅ ⌞ Q ⌟)
    → is-monotone P Q (f #_)
    → is-order-reflection P Q (f #_)
    → P ≅ Q
  iso-mono-refl→≅ f mo or =
    iso-order-embedding→≅ f $
    monotone-reflection→is-order-embedding {P = P} {Q = Q} (f #_) mo or

  surj-order-embedding→≅
    : (f : ⌞ P ⌟ ↠ ⌞ Q ⌟)
    → is-order-embedding P Q (f #_)
    → P ≅ Q
  surj-order-embedding→≅ f oe =
    iso-order-embedding→≅
      (≃→≅ $ f #_ , is-surjective-embedding→is-equiv (f .snd)
                       (is-order-embedding→is-embedding {P = P} {Q = Q} (f .fst) oe))
      oe
