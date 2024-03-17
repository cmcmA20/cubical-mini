{-# OPTIONS --safe #-}
module Order.Base where

open import Categories.Prelude
import Categories.Morphism

open import Structures.IdentitySystem

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
    ob-is-set = identity-system→is-of-hlevel 1
      {r = λ _ → ≤-refl , ≤-refl}
      (set-identity-system hlevel! (≤-antisym $ₜ²_))
      hlevel!

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

  proj-hlevel-poset-ob : Struct-proj-desc (quote is-of-hlevel) by-hlevel (quote Poset.Ob) false
  proj-hlevel-poset-ob .Struct-proj-desc.struct-name = quote Poset
  proj-hlevel-poset-ob .Struct-proj-desc.struct-args-length = 2
  proj-hlevel-poset-ob .Struct-proj-desc.goal-projection = quote Poset.ob-is-set
  proj-hlevel-poset-ob .Struct-proj-desc.projection-args-length = 3
  proj-hlevel-poset-ob .Struct-proj-desc.level-selector = inl 2
  proj-hlevel-poset-ob .Struct-proj-desc.carrier-selector = 2

  proj-hlevel-poset-≤ : Struct-proj-desc (quote is-of-hlevel) by-hlevel (quote Poset._≤_) false
  proj-hlevel-poset-≤ .Struct-proj-desc.struct-name = quote Poset
  proj-hlevel-poset-≤ .Struct-proj-desc.struct-args-length = 2
  proj-hlevel-poset-≤ .Struct-proj-desc.goal-projection = quote Poset.≤-thin
  proj-hlevel-poset-≤ .Struct-proj-desc.projection-args-length = 5
  proj-hlevel-poset-≤ .Struct-proj-desc.level-selector = inl 1
  proj-hlevel-poset-≤ .Struct-proj-desc.carrier-selector = 2


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

unquoteDecl monotone-iso = declare-record-iso monotone-iso (quote Monotone)

private variable
  P Q R : Poset o ℓ

monotone-is-set : is-set (Monotone P Q)
monotone-is-set {Q} = iso→is-of-hlevel 2 monotone-iso
  (Σ-is-of-hlevel 2 hlevel! λ _ → is-prop→is-set hlevel!)

instance
  H-Level-Monotone : ∀ {n} → H-Level (2 + n) (Monotone P Q)
  H-Level-Monotone = hlevel-basic-instance 2 monotone-is-set

  Funlike-Monotone : Funlike ur (Monotone P Q) ⌞ P ⌟ (λ _ → ⌞ Q ⌟)
  Funlike-Monotone ._#_ = hom

monotone-pathP
  : {P : I → Poset o ℓ} {Q : I → Poset o′ ℓ′}
  → {f : Monotone (P i0) (Q i0)} {g : Monotone (P i1) (Q i1)}
  → ＜ f $_ ／ (λ i → ⌞ P i ⌟ → ⌞ Q i ⌟) ＼ g $_ ＞
  → ＜ f ／ (λ i → Monotone (P i) (Q i)) ＼ g ＞
monotone-pathP q i .hom a = q i a
monotone-pathP {P} {Q} {f} {g} q i .Monotone.pres-≤ {x} {y} α =
  is-prop→pathP
    (λ i → Π³-is-of-hlevel {A = ⌞ P i ⌟} {B = λ _ → ⌞ P i ⌟} {C = λ x y → P i .Poset._≤_ x y} 1
      λ x y _ → Q i .Poset.≤-thin {q i x} {q i y})
    (λ _ _ α → f .Monotone.pres-≤ α)
    (λ _ _ α → g .Monotone.pres-≤ α) i x y α

Extensional-Monotone
  : ∀ {ℓr} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
  → ⦃ sa : Extensional (P →̇ Q) ℓr ⦄
  → Extensional (Monotone P Q) ℓr
Extensional-Monotone ⦃ sa ⦄ = set-injective→extensional! monotone-pathP sa

instance
  Extensionality-Monotone : {P : Poset o ℓ} {Q : Poset o′ ℓ′}
                          → Extensionality (Monotone P Q)
  Extensionality-Monotone = record { lemma = quote Extensional-Monotone }


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
