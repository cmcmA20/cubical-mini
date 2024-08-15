{-# OPTIONS --safe --no-exact-split #-}
module Order.Base where

open import Categories.Prelude
import Categories.Morphism

open import Meta.Projection
open import Meta.Reflection.Base

open import Data.Bool.Base
open import Data.Sum.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Name
open import Data.Reflection.Term

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

    Refl-≤ : Refl _≤_
    Refl-≤ .refl = ≤-refl

    Trans-≤ : Transitive _≤_
    Trans-≤ ._∙_ = ≤-trans

    ⇒-Hom : ⇒-notation Ob Ob (𝒰 ℓ)
    ⇒-Hom ._⇒_ = _≤_

  opaque
    ob-is-set : is-set Ob
    ob-is-set = identity-system→is-of-hlevel! 1
      {r = λ _ → ≤-refl , ≤-refl}
      (set-identity-system! (≤-antisym $ₜ²_))

    ≤-refl′ : ∀ {x y} → x ＝ y → x ≤ y
    ≤-refl′ {x} p = subst (x ≤_) p ≤-refl

  instance
    H-Level-poset-ob : ⦃ n ≥ʰ 2 ⦄ → H-Level n Ob
    H-Level-poset-ob ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 ob-is-set

unquoteDecl poset-iso = declare-record-iso poset-iso (quote Poset)

private variable
  o o′ o″ ℓ ℓ′ ℓ″ : Level

instance
  Underlying-Poset : Underlying (Poset o ℓ)
  Underlying-Poset .Underlying.ℓ-underlying = _
  Underlying-Poset .Underlying.⌞_⌟ = Poset.Ob

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
  constructor mk-monotone
  private
    module P = Poset P
    module Q = Poset Q
  field
    hom    : P.Ob → Q.Ob
    pres-≤ : ∀ {x y} → x P.≤ y → hom x Q.≤ hom y
{-# INLINE mk-monotone #-}

open Monotone public

unquoteDecl H-Level-Monotone =
  declare-record-hlevel 2 H-Level-Monotone (quote Monotone)

private variable P Q R : Poset o ℓ

instance
  ⇒-Poset : ⇒-notation (Poset o ℓ) (Poset o′ ℓ′) (Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⇒-Poset ._⇒_ = Monotone

  Funlike-Monotone : Funlike ur (P ⇒ Q) ⌞ P ⌟ (λ _ → ⌞ Q ⌟)
  Funlike-Monotone ._#_ = hom

  Refl-Monotone : Refl {A = Poset o ℓ} Monotone
  Refl-Monotone .refl .hom = refl
  Refl-Monotone .refl .pres-≤ = refl

  Trans-Monotone : Trans (Monotone {o} {o′} {ℓ} {ℓ′})
                         (Monotone {o′ = o″} {ℓ′ = ℓ″})
                         Monotone
  Trans-Monotone ._∙_ f g .hom x = g $ f $ x
  Trans-Monotone ._∙_ f g .pres-≤ x≤y = g .pres-≤ (f .pres-≤ x≤y)

monotone-pathᴾ
  : {P : I → Poset o ℓ} {Q : I → Poset o′ ℓ′}
    {f : Monotone (P i0) (Q i0)} {g : Monotone (P i1) (Q i1)}
  → ＜ f $_ ／ (λ i → ⌞ P i ⌟ → ⌞ Q i ⌟) ＼ g $_ ＞
  → ＜ f ／ (λ i → Monotone (P i) (Q i)) ＼ g ＞
monotone-pathᴾ q i .hom a = q i a
monotone-pathᴾ {P} {Q} {f} {g} q i .pres-≤ {x} {y} α =
  is-prop→pathᴾ
    (λ i → Π³-is-of-hlevel {A = ⌞ P i ⌟} {B = λ _ → ⌞ P i ⌟} {C = λ x y → P i .Poset._≤_ x y} 1
      λ x y _ → Q i .Poset.≤-thin {q i x} {q i y})
    (λ _ _ α → f .pres-≤ α)
    (λ _ _ α → g .pres-≤ α) i x y α

instance
  Extensional-Monotone
    : ∀ {ℓr} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
    → ⦃ sa : Extensional (⌞ P ⌟ ⇒ ⌞ Q ⌟) ℓr ⦄
    → Extensional (P ⇒ Q) ℓr
  Extensional-Monotone ⦃ sa ⦄ = set-injective→extensional! monotone-pathᴾ sa


Posets : (o ℓ : Level) → Precategory (ℓsuc o ⊔ ℓsuc ℓ) (o ⊔ ℓ)
Posets o ℓ .Precategory.Ob = Poset o ℓ
Posets o ℓ .Precategory.Hom = Monotone
Posets o ℓ .Precategory.Hom-set = hlevel!
Posets o ℓ .Precategory.id  = refl
Posets o ℓ .Precategory._∘_ = _∘ˢ_
Posets o ℓ .Precategory.id-r _ = trivial!
Posets o ℓ .Precategory.id-l _ = trivial!
Posets o ℓ .Precategory.assoc _ _ _ = trivial!

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

𝟘ₚ : Poset o ℓ
𝟘ₚ .Poset.Ob = ⊥
𝟘ₚ .Poset._≤_ _ _ = ⊥
𝟘ₚ .Poset.≤-thin = hlevel 1

𝟙ₚ : Poset o ℓ
𝟙ₚ .Poset.Ob = ⊤
𝟙ₚ .Poset._≤_ _ _ = ⊤
𝟙ₚ .Poset.≤-thin = hlevel 1
𝟙ₚ .Poset.≤-refl = _
𝟙ₚ .Poset.≤-trans = _
𝟙ₚ .Poset.≤-antisym _ _ = refl
