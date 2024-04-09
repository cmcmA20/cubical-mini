{-# OPTIONS --safe --backtracking-instance-search #-}
module Order.Base where

open import Categories.Prelude
import Categories.Morphism

open import Meta.Projection
open import Meta.Reflection.Base

open import Data.Bool.Base

private variable n : HLevel

record Poset o ℓ : 𝒰 (ℓsuc (o ⊔ ℓ)) where
  no-eta-equality
  field
    Ob  : 𝒰 o
    _≤_ : Ob → Ob → 𝒰 ℓ
    ≤-thin    : ∀ {x y} → is-prop (x ≤ y)
    ≤-refl    : ∀ {x} → x ≤ x
    ≤-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ＝ y

  instance
    H-Level-≤-prop : ∀ {x y} → H-Level (suc n) (x ≤ y)
    H-Level-≤-prop = hlevel-prop-instance ≤-thin

  opaque
    ob-is-set : is-set Ob
    ob-is-set = identity-system→is-of-hlevel! 1
      {r = λ _ → ≤-refl , ≤-refl}
      (set-identity-system! (≤-antisym $ₜ²_))

    ≤-refl′ : ∀ {x y} → x ＝ y → x ≤ y
    ≤-refl′ {x} p = subst (x ≤_) p ≤-refl

  instance
    H-Level-poset-ob : H-Level (2 + n) Ob
    H-Level-poset-ob = hlevel-basic-instance 2 ob-is-set

unquoteDecl poset-iso = declare-record-iso poset-iso (quote Poset)

private variable
  o o′ ℓ ℓ′ : Level

instance
  Underlying-Poset : Underlying (Poset o ℓ)
  Underlying-Poset .Underlying.ℓ-underlying = _
  Underlying-Poset .Underlying.⌞_⌟⁰ = Poset.Ob

  open Struct-proj-desc

  hlevel-proj-poset-ob : Struct-proj-desc true (quote Poset.Ob)
  hlevel-proj-poset-ob .has-level = quote Poset.ob-is-set
  hlevel-proj-poset-ob .upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-poset-ob .get-level _ = pure (lit (nat 2))
  hlevel-proj-poset-ob .get-argument (_ ∷ _ ∷ x v∷ _) = pure x
  hlevel-proj-poset-ob .get-argument _ = type-error []

  hlevel-proj-poset-hom : Struct-proj-desc true (quote Poset._≤_)
  hlevel-proj-poset-hom .has-level = quote Poset.≤-thin
  hlevel-proj-poset-hom .upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-poset-hom .get-level _ = pure (lit (nat 1))
  hlevel-proj-poset-hom .get-argument (_ ∷ _ ∷ x v∷ _) = pure x
  hlevel-proj-poset-hom .get-argument _ = type-error []


record Monotone {o o′ ℓ ℓ′}
  (P : Poset o ℓ) (Q : Poset o′ ℓ′) : 𝒰 (o ⊔ o′ ⊔ ℓ ⊔ ℓ′) where
  no-eta-equality
  private
    module P = Poset P
    module Q = Poset Q
  field
    hom    : P.Ob → Q.Ob
    pres-≤ : ∀ {x y} → x P.≤ y → hom x Q.≤ hom y

open Monotone public

instance
  unquoteDecl H-Level-Monotone =
    declare-record-hlevel 2 H-Level-Monotone (quote Monotone)

private variable
  P Q R : Poset o ℓ

instance
  Funlike-Monotone : Funlike ur (Monotone P Q) ⌞ P ⌟ (λ _ → ⌞ Q ⌟)
  Funlike-Monotone ._#_ = hom

monotone-pathᴾ
  : {P : I → Poset o ℓ} {Q : I → Poset o′ ℓ′}
  → {f : Monotone (P i0) (Q i0)} {g : Monotone (P i1) (Q i1)}
  → ＜ f $_ ／ (λ i → ⌞ P i ⌟ → ⌞ Q i ⌟) ＼ g $_ ＞
  → ＜ f ／ (λ i → Monotone (P i) (Q i)) ＼ g ＞
monotone-pathᴾ q i .hom a = q i a
monotone-pathᴾ {P} {Q} {f} {g} q i .Monotone.pres-≤ {x} {y} α =
  is-prop→pathᴾ
    (λ i → Π³-is-of-hlevel {A = ⌞ P i ⌟} {B = λ _ → ⌞ P i ⌟} {C = λ x y → P i .Poset._≤_ x y} 1
      λ x y _ → Q i .Poset.≤-thin {q i x} {q i y})
    (λ _ _ α → f .Monotone.pres-≤ α)
    (λ _ _ α → g .Monotone.pres-≤ α) i x y α

instance
  Extensional-Monotone
    : ∀ {ℓr} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
    → ⦃ sa : Extensional (P →̇ Q) ℓr ⦄
    → Extensional (Monotone P Q) ℓr
  Extensional-Monotone ⦃ sa ⦄ = set-injective→extensional! monotone-pathᴾ sa


idₘ : Monotone P P
idₘ .hom    x   = x
idₘ .pres-≤ x≤y = x≤y

_∘ₘ_ : Monotone Q R → Monotone P Q → Monotone P R
(f ∘ₘ g) .hom    x   = f $ g $ x
(f ∘ₘ g) .pres-≤ x≤y = f .pres-≤ $ g .pres-≤ x≤y

Posets : (o ℓ : Level) → Precategory (ℓsuc o ⊔ ℓsuc ℓ) (o ⊔ ℓ)
Posets o ℓ .Precategory.Ob = Poset o ℓ
Posets o ℓ .Precategory.Hom = Monotone
Posets o ℓ .Precategory.Hom-set = hlevel!
Posets o ℓ .Precategory.id  = idₘ
Posets o ℓ .Precategory._∘_ = _∘ₘ_
Posets o ℓ .Precategory.id-r _ = trivial!
Posets o ℓ .Precategory.id-l _ = trivial!
Posets o ℓ .Precategory.assoc _ _ _ = trivial!

-- TODO add `Reasoning` if needed
module Posets {o ℓ} = Categories.Morphism (Posets o ℓ)

Forget-poset : ∀ {o ℓ} → Functor (Posets o ℓ) (Sets o)
Forget-poset .Functor.F₀ P = el! ⌞ P ⌟
Forget-poset .Functor.F₁ = hom
Forget-poset .Functor.F-id = refl
Forget-poset .Functor.F-∘ _ _ = refl

_ᵒᵖᵖ : Poset o ℓ → Poset o ℓ
(P ᵒᵖᵖ) .Poset.Ob = Poset.Ob P
(P ᵒᵖᵖ) .Poset._≤_ = flip (Poset._≤_ P)
(P ᵒᵖᵖ) .Poset.≤-thin = Poset.≤-thin P
(P ᵒᵖᵖ) .Poset.≤-refl = Poset.≤-refl P
(P ᵒᵖᵖ) .Poset.≤-trans = flip (Poset.≤-trans P)
(P ᵒᵖᵖ) .Poset.≤-antisym = flip (Poset.≤-antisym P)
