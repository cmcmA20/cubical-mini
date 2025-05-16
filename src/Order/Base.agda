{-# OPTIONS --safe --no-exact-split #-}
module Order.Base where

open import Cat.Prelude
import Cat.Morphism

open import Meta.Effect
open import Meta.Projection
open import Meta.Reflection.Base

open import Data.Bool.Base
open import Data.Sum.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Name
open import Data.Reflection.Term

private variable
  n : HLevel
  ℓ : Level
  A : Type ℓ
  x y z : A

record Poset o ℓ : 𝒰 (ℓsuc (o ⊔ ℓ)) where
  no-eta-equality
  infix 4.5 _≤_
  field
    Ob  : 𝒰 o
    _≤_ : Ob → Ob → 𝒰 ℓ
    ≤-thin    : is-prop (x ≤ y)
    ≤-refl    : x ≤ x
    ≤-trans   : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ＝ y

  opaque
    instance
      H-Level-≤-prop : H-Level (suc n) (x ≤ y)
      H-Level-≤-prop = hlevel-prop-instance ≤-thin

    ob-is-set : is-set Ob
    ob-is-set = identity-system→is-of-hlevel! 1
      {R = λ x y → (x ≤ y) × (y ≤ x)}
      {r = λ _ → ≤-refl , ≤-refl}
      (set-identity-system! (≤-antisym $ₜ²_))

    instance
      H-Level-poset-ob : ⦃ n ≥ʰ 2 ⦄ → H-Level n Ob
      H-Level-poset-ob ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 ob-is-set

  instance
    Refl-≤ : Refl _≤_
    Refl-≤ .refl = ≤-refl
    {-# OVERLAPPING Refl-≤ #-}

    Trans-≤ : Trans _≤_
    Trans-≤ ._∙_ = ≤-trans
    {-# OVERLAPPING Trans-≤ #-}

    HAssoc-≤ : HAssoc _≤_
    HAssoc-≤ .∙-assoc _ _ _ = prop!

    HUnit-o-≤ : HUnit-o _≤_
    HUnit-o-≤ .∙-id-o _ = prop!

    HUnit-i-≤ : HUnit-i _≤_
    HUnit-i-≤ .∙-id-i _ = prop!

    ⇒-Hom : ⇒-notation Ob Ob (𝒰 ℓ)
    ⇒-Hom .⇒-notation.Constraint _ _ = ⊤
    ⇒-Hom ._⇒_ x y = x ≤ y
    {-# OVERLAPPING ⇒-Hom #-}

    ≅-Poset-Ob : ≅-notation Ob Ob (𝒰 ℓ)
    ≅-Poset-Ob ._≅_ = Iso _≤_ _≤_
    {-# OVERLAPPING ≅-Poset-Ob #-}

  _≥_ _≰_ _≱_ : Ob → Ob → 𝒰 ℓ
  _≥_ = flip _≤_
  _≰_ x y = ¬ x ≤ y
  _≱_ x y = ¬ x ≥ y

  infixr 2 _≤⟨_⟩_
  _≤⟨_⟩_ : ∀ x {y z} → x ≤ y → y ≤ z → x ≤ z
  f ≤⟨ p ⟩ q = p ∙ q

  =→≤ : x ＝ y → x ≤ y
  =→≤ = =→~

  =→≥ : x ＝ y → y ≤ x
  =→≥ = =→~⁻

  ≤≠→≱ : x ≤ y → x ≠ y → x ≱ y
  ≤≠→≱ x≤y x≠y x≥y = ⊥.rec (x≠y (≤-antisym x≤y x≥y))

unquoteDecl poset-iso = declare-record-iso poset-iso (quote Poset)

private variable o o′ o″ o‴ ℓ′ ℓ″ ℓ‴ : Level

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

  Dual-Poset : Has-unary-op (Poset o ℓ)
  Dual-Poset .minv P .Poset.Ob = P .Poset.Ob
  Dual-Poset .minv P .Poset._≤_ = flip (P .Poset._≤_)
  Dual-Poset .minv P .Poset.≤-thin = P. Poset.≤-thin
  Dual-Poset .minv P .Poset.≤-refl = P .Poset.≤-refl
  Dual-Poset .minv P .Poset.≤-trans = flip (P. Poset.≤-trans)
  Dual-Poset .minv P .Poset.≤-antisym = flip (P .Poset.≤-antisym)

  Invol-Dual-Poset : Invol (Poset o ℓ)
  Invol-Dual-Poset .minv-invol P _ .Poset.Ob = P .Poset.Ob
  Invol-Dual-Poset .minv-invol P _ .Poset._≤_ = P .Poset._≤_
  Invol-Dual-Poset .minv-invol P _ .Poset.≤-thin = P .Poset.≤-thin
  Invol-Dual-Poset .minv-invol P _ .Poset.≤-refl = P .Poset.≤-refl
  Invol-Dual-Poset .minv-invol P _ .Poset.≤-trans = P .Poset.≤-trans
  Invol-Dual-Poset .minv-invol P _ .Poset.≤-antisym = P .Poset.≤-antisym

  ⊥-Poset : ⊥-notation (Poset o ℓ)
  ⊥-Poset .⊥ .Poset.Ob = ⊥
  ⊥-Poset .⊥ .Poset._≤_ _ _ = ⊥

  ⊤-Poset : ⊤-notation (Poset o ℓ)
  ⊤-Poset .⊤ .Poset.Ob = ⊤
  ⊤-Poset .⊤ .Poset._≤_ _ _ = ⊤
  ⊤-Poset .⊤ .Poset.≤-thin = hlevel 1
  ⊤-Poset .⊤ .Poset.≤-refl = _
  ⊤-Poset .⊤ .Poset.≤-trans = _
  ⊤-Poset .⊤ .Poset.≤-antisym _ _ = refl


module _ (P : Poset o ℓ) (Q : Poset o′ ℓ′) where
  private
    module P = Poset P
    module Q = Poset Q

  is-monotone : (f : ⌞ P ⌟ → ⌞ Q ⌟) → Type _
  is-monotone f = ∀{x y} → x ⇒ y → f x ⇒ f y

  record Monotone : 𝒰 (o ⊔ o′ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    constructor mk-monotone
    field
      hom    : P.Ob → Q.Ob
      pres-≤ : is-monotone hom
  {-# INLINE mk-monotone #-}

open Monotone public

unquoteDecl H-Level-Monotone =
  declare-record-hlevel 2 H-Level-Monotone (quote Monotone)
unquoteDecl Monotone-Iso = declare-record-iso Monotone-Iso (quote Monotone)

private variable P Q R : Poset o ℓ

instance
  ⇒-Poset : ⇒-notation (Poset o ℓ) (Poset o′ ℓ′) (Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⇒-Poset .⇒-notation.Constraint _ _ = ⊤
  ⇒-Poset ._⇒_ P Q = Monotone P Q

  Dual-Monotone : Dual {A = Poset o ℓ} {B = Poset o′ ℓ′} Monotone λ Q P → Monotone (P ᵒᵖ) (Q ᵒᵖ)
  Dual-Monotone ._ᵒᵖ F .hom = F .hom
  Dual-Monotone ._ᵒᵖ F .pres-≤ = F .pres-≤

  Dual-Monotone⁻ : Dual {A = Poset o ℓ} {B = Poset o′ ℓ′} (λ Q P → Monotone (P ᵒᵖ) (Q ᵒᵖ)) Monotone
  Dual-Monotone⁻ ._ᵒᵖ F .hom = F .hom
  Dual-Monotone⁻ ._ᵒᵖ F .pres-≤ = F .pres-≤
  {-# INCOHERENT Dual-Monotone⁻ #-}

  Funlike-Monotone₀ : Funlike ur (P ⇒ Q) ⌞ P ⌟ (λ _ → ⌞ Q ⌟)
  Funlike-Monotone₀ ._#_ = hom

  Funlike-Monotone₁
    : Funlike ur (P ⇒ Q) (Poset._≤_ P x y) (λ (f , _) → Poset._≤_ Q (f # x) (f # y))
  Funlike-Monotone₁ ._#_ x≤y = x≤y .pres-≤

  GInvol-Dual-Monotone : GInvol {A = Poset o ℓ} {B = Poset o′ ℓ′} Monotone (λ Q′ P′ → Monotone (P′ ᵒᵖ) (Q′ ᵒᵖ))
  GInvol-Dual-Monotone .invol F _ .hom = F .hom
  GInvol-Dual-Monotone .invol F _ .pres-≤ = F .pres-≤

  Refl-Monotone : Refl {A = Poset o ℓ} Monotone
  Refl-Monotone .refl .hom = refl
  Refl-Monotone .refl .pres-≤ = refl

  Comp-Monotone : Comp (Monotone {o} {o′} {ℓ} {ℓ′})
                         (Monotone {o′ = o″} {ℓ′ = ℓ″})
                         Monotone
  Comp-Monotone ._∙_ f g .hom x = g $ f $ x
  Comp-Monotone ._∙_ f g .pres-≤ x≤y = g $ f $ x≤y

  GAssoc-Monotone
    : GAssoc {A = Poset o ℓ} {B = Poset o′ ℓ′}
             {C = Poset o″ ℓ″} {D = Poset o‴ ℓ‴}
             Monotone Monotone Monotone Monotone Monotone Monotone
  GAssoc-Monotone .∙-assoc F G H = Equiv.injective (≅ₜ→≃ Monotone-Iso) (refl ,ₚ prop!)

  GUnit-o-Monotone : GUnit-o {A = Poset o ℓ} {B = Poset o′ ℓ′} Monotone Monotone
  GUnit-o-Monotone .∙-id-o F = Equiv.injective (≅ₜ→≃ Monotone-Iso) (refl ,ₚ prop!)

  GUnit-i-Monotone : GUnit-i {A = Poset o ℓ} {B = Poset o′ ℓ′} Monotone Monotone
  GUnit-i-Monotone .∙-id-i F = Equiv.injective (≅ₜ→≃ Monotone-Iso) (refl ,ₚ prop!)

  ≅-Poset : ≅-notation (Poset o ℓ) (Poset o′ ℓ′) _
  ≅-Poset ._≅_ = Iso Monotone Monotone

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
    (λ _ _ α → f # α)
    (λ _ _ α → g # α) i x y α

instance
  Extensional-Monotone
    : ∀ {ℓr} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
    → ⦃ sa : Extensional (⌞ P ⌟ ⇒ ⌞ Q ⌟) ℓr ⦄
    → Extensional (P ⇒ Q) ℓr
  Extensional-Monotone ⦃ sa ⦄ = set-injective→extensional! monotone-pathᴾ sa

record _=>ₚ_ {P : Poset o ℓ}
             {Q : Poset o′ ℓ′}
             (F G : Monotone P Q)
      : Type (o ⊔ ℓ ⊔ ℓ′)
  where
  no-eta-equality
  constructor NTₚ
  private
    module P = Poset P
    open module Q = Poset Q

  field η : (x : P.Ob) → F # x ≤ G # x

{-# INLINE NTₚ #-}

unquoteDecl H-Level-NTₚ = declare-record-hlevel 1 H-Level-NTₚ (quote _=>ₚ_)

instance
  ⇒-ntₚ : ⇒-notation (P ⇒ Q) (P ⇒ Q) _
  ⇒-ntₚ .⇒-notation.Constraint _ _ = ⊤
  ⇒-ntₚ ._⇒_ α β = α =>ₚ β

  Dual-ntₚ
    : {P : Poset o ℓ} {Q : Poset o′ ℓ′}
    → Dual {A = Monotone P Q} {B = Monotone P Q} _=>ₚ_ λ G F → G ᵒᵖ =>ₚ F ᵒᵖ
  Dual-ntₚ ._ᵒᵖ α ._=>ₚ_.η = α ._=>ₚ_.η

  Funlike-ntₚ
    : {P : Poset o ℓ} {Q : Poset o′ ℓ′} {F G : P ⇒ Q}
    → Funlike ur (F ⇒ G) ⌞ P ⌟ (λ (_ , x) → Q .Poset._≤_ (F $ x) (G $ x))
  Funlike-ntₚ ._#_ = _=>ₚ_.η

  Refl-ntₚ : Refl (_=>ₚ_ {P = P} {Q = Q})
  Refl-ntₚ {Q} .refl ._=>ₚ_.η _ = Poset.≤-refl Q

  Comp-ntₚ : Comp (_=>ₚ_ {P = P} {Q = Q}) _=>ₚ_ _=>ₚ_
  Comp-ntₚ {Q} ._∙_ α β ._=>ₚ_.η x = α # x ∙ β # x
    where open Poset Q

  Whisker-i-Monotone-ntₚ
    : {X : Poset o ℓ} {P : Poset o′ ℓ′} {Q : Poset o″ ℓ″}
    → Whisker-i
        Monotone Monotone Monotone (λ _ _ → ⊤) _ _
        X P Q Q
        (λ _ → _=>ₚ_) (λ _ → _=>ₚ_)
  Whisker-i-Monotone-ntₚ ._◁_ H α ._=>ₚ_.η x = α # (H # x)

  Whisker-o-Monotone-ntₚ
    : {P : Poset o ℓ} {Q : Poset o′ ℓ′} {X : Poset o″ ℓ″}
    → Whisker-o
        Monotone Monotone (λ _ _ → ⊤) Monotone _ _
        P P Q X
        (λ _ → _=>ₚ_)
        (λ _ → _=>ₚ_)
  Whisker-o-Monotone-ntₚ ._▷_ α K ._=>ₚ_.η x = K # (α # x)

  -- Galois connection
  ⊣-Monotone
    : {P : Poset o ℓ} {Q : Poset o′ ℓ′}
    → ⊣-notation (Monotone P Q) (Monotone Q P) (𝒰 (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⊣-Monotone {P} {Q} ._⊣_ L R = Adjoint Monotone Monotone Monotone Monotone P P._≤_ Q Q._≤_ L R _=>ₚ_ _=>ₚ_
    where
    module P = Poset P
    module Q = Poset Q

Posets : (o ℓ : Level) → Precategory (ℓsuc o ⊔ ℓsuc ℓ) (o ⊔ ℓ)
Posets o ℓ .Precategory.Ob = Poset o ℓ
Posets o ℓ .Precategory.Hom = Monotone
Posets o ℓ .Precategory.id  = refl
Posets o ℓ .Precategory._∘_ = _∘ˢ_
Posets o ℓ .Precategory.id-r _ = trivial!
Posets o ℓ .Precategory.id-l _ = trivial!
Posets o ℓ .Precategory.assoc _ _ _ = trivial!

Forget-poset : ∀ {o ℓ} → Posets o ℓ ⇒ Sets o
Forget-poset .Functor.F₀ P = el! ⌞ P ⌟
Forget-poset .Functor.F₁ = hom
Forget-poset .Functor.F-id = refl
Forget-poset .Functor.F-∘ _ _ = refl
