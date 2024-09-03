{-# OPTIONS --safe --no-exact-split #-}
module Structures.n-Type where

open import Meta.Prelude
open import Meta.Effect.Alt
open import Meta.Extensionality
open import Meta.Projection
open import Meta.Record
open import Meta.Reflection

open import Data.Empty.Base
open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Reflection.Argument
open import Data.Reflection.Error
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Literal
open import Data.Reflection.Name
open import Data.Reflection.Term
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Truncation.Propositional.Base
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  m n k : HLevel

record n-Type (ℓ : Level) (n : HLevel) : Type (ℓsuc ℓ) where
  constructor el
  field
    carrier : Type ℓ
    carrier-is-tr : is-of-hlevel n carrier

open n-Type

unquoteDecl n-Type-iso = declare-record-iso n-Type-iso (quote n-Type)

private variable
  X Y : n-Type ℓ n

instance
  Underlying-n-Type : Underlying (n-Type ℓ n)
  Underlying-n-Type {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-n-Type .⌞_⌟ = carrier

  Refl-n-Fun : Refl {A = n-Type ℓ n} λ X Y → Fun ⌞ X ⌟ ⌞ Y ⌟
  Refl-n-Fun .refl x = x
  {-# INCOHERENT Refl-n-Fun #-}

  Trans-n-Fun
    : Trans {A = n-Type ℓ n} {B = n-Type ℓ′ n} {C = n-Type ℓ″ n}
        (λ X Y → Fun ⌞ X ⌟ ⌞ Y ⌟) (λ X Y → Fun ⌞ X ⌟ ⌞ Y ⌟) (λ X Y → Fun ⌞ X ⌟ ⌞ Y ⌟)
  Trans-n-Fun ._∙_ f g x = g (f x)
  {-# INCOHERENT Trans-n-Fun #-}

  ×-n-Type : ×-notation (n-Type ℓ n) (n-Type ℓ′ n) (n-Type (ℓ ⊔ ℓ′) n)
  ×-n-Type ._×_ (el A p) (el B q) = el (A × B) (×-is-of-hlevel _ p q)

  ⇒-n-Type : ⇒-notation (n-Type ℓ m) (n-Type ℓ′ n) (n-Type (ℓ ⊔ ℓ′) n)
  ⇒-n-Type ._⇒_ (el A _) (el B q) = el (A ⇒ B) (fun-is-of-hlevel _ q)

  ⊎-n-Type : ⦃ 2 ≤ʰ n ⦄ → ⊎-notation (n-Type ℓ n) (n-Type ℓ′ n) (n-Type (ℓ ⊔ ℓ′) n)
  ⊎-n-Type ⦃ s≤ʰs (s≤ʰs _) ⦄ ._⊎_ (el A p) (el B q) = el (A ⊎ B) (⊎-is-of-hlevel _ p q)

  ⊎₁-n-Type : ⦃ z : 1 ≤ʰ k ⦄ → ⊎₁-notation (n-Type ℓ m) (n-Type ℓ′ n) (n-Type (ℓ ⊔ ℓ′) k)
  ⊎₁-n-Type ⦃ z = s≤ʰs _ ⦄ ._⊎₁_ (el A _) (el B _) = el (A ⊎₁ B) (is-prop→is-of-hlevel-suc squash₁)

  ¬-n-Type : ⦃ z : 1 ≤ʰ n ⦄ → ¬-notation (n-Type ℓ m) (n-Type ℓ n)
  ¬-n-Type ⦃ z = s≤ʰs _ ⦄ .¬_ (el A _) = el (¬ A) (fun-is-of-hlevel _ (hlevel _))

  Π-n-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Π-notation A (n-Type ℓ′ n) (n-Type (ua .ℓ-underlying ⊔ ℓ′) n)
  Π-n-Type .Π-notation.Π X F = el (Π[ a ꞉ X ] ⌞ F a ⌟) (Π-is-of-hlevel _ λ x → F x .carrier-is-tr)

  ∀-n-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → ∀-notation A (n-Type ℓ′ n) (n-Type (ua .ℓ-underlying ⊔ ℓ′) n)
  ∀-n-Type .∀-notation.∀′ X F = el (∀[ a ꞉ X ] ⌞ F a ⌟) (∀-is-of-hlevel _ λ x → F x .carrier-is-tr)

  Σ-n-Type : Σ-notation (n-Type ℓ n) (n-Type ℓ′ n) (n-Type (ℓ ⊔ ℓ′) n)
  Σ-n-Type .Σ-notation.Σ A F = el (Σ[ a ꞉ A ] ⌞ F a ⌟) (Σ-is-of-hlevel _ (A .carrier-is-tr) (λ x → F x .carrier-is-tr))

  ∃-n-Type
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄ ⦃ z : 1 ≤ʰ k ⦄
    → ∃-notation A (n-Type ℓ′ n) (n-Type (ua .ℓ-underlying ⊔ ℓ′) k)
  ∃-n-Type ⦃ z = s≤ʰs _ ⦄ .∃-notation.∃ X F = el (∃[ a ꞉ X ] ⌞ F a ⌟) (is-prop→is-of-hlevel-suc squash₁)

  ⊥-n-Type-small : ⦃ _ : 1 ≤ʰ n ⦄ → ⊥-notation (n-Type 0ℓ n)
  ⊥-n-Type-small ⦃ s≤ʰs _ ⦄ .⊥ = el ⊥ (hlevel _)
  {-# OVERLAPPING ⊥-n-Type-small #-}

  ⊥-n-Type : ⦃ _ : 1 ≤ʰ n ⦄ → ⊥-notation (n-Type ℓ n)
  ⊥-n-Type ⦃ s≤ʰs _ ⦄ .⊥ = el (Lift _ ⊥) (hlevel _)
  {-# INCOHERENT ⊥-n-Type #-}

  ⊤-n-Type-small : ⊤-notation (n-Type 0ℓ n)
  ⊤-n-Type-small .⊤ = el ⊤ (hlevel _)
  {-# OVERLAPPING ⊤-n-Type-small #-}

  ⊤-n-Type : ⊤-notation (n-Type ℓ n)
  ⊤-n-Type .⊤ = el ⊤ (hlevel _)
  {-# INCOHERENT ⊤-n-Type #-}

n-path : {X Y : n-Type ℓ n} → ⌞ X ⌟ ＝ ⌞ Y ⌟ → X ＝ Y
n-path f i .carrier = f i
n-path {n} {X} {Y} f i .carrier-is-tr =
  is-prop→pathᴾ (λ i → is-of-hlevel-is-prop {A = f i} n) (X .carrier-is-tr) (Y .carrier-is-tr) i

-- FIXME rewrite without cubes
n-path-refl : {X : n-Type ℓ n} → n-path {X = X} refl ＝ refl
n-path-refl {X} _ _ .carrier = X .carrier
n-path-refl {n} {X} i j .carrier-is-tr = θ j i where
  p = is-prop→pathᴾ (λ _ → is-of-hlevel-is-prop n) (X .carrier-is-tr) _
  θ : Square p reflₚ reflₚ refl
  θ = is-prop→squareᴾ (λ _ _ → is-of-hlevel-is-prop n) _ _ _ _

@0 n-ua : ⌞ X ⌟ ≃ ⌞ Y ⌟ → X ＝ Y
n-ua f = n-path (ua f)

instance
  @0 Extensional-n-Type : ∀ {n} → Extensional (n-Type ℓ n) ℓ
  Extensional-n-Type .Pathᵉ A B = Pathᵉ Extensional-Type ⌞ A ⌟ ⌞ B ⌟
  Extensional-n-Type .reflᵉ _ = refl
  Extensional-n-Type .idsᵉ .to-path = n-ua
  Extensional-n-Type .idsᵉ .to-path-over = Extensional-Type .idsᵉ .to-path-over
  {-# OVERLAPPABLE Extensional-n-Type #-}

  @0 Extensional-Prop : Extensional (n-Type ℓ 1) ℓ
  Extensional-Prop .Pathᵉ (el A _) (el B _) = (A → B) × (B → A)
  Extensional-Prop .reflᵉ _ = refl , refl
  Extensional-Prop .idsᵉ .to-path {a = el A p} {b = el B q} (f , g) =
    Equiv.injective (≅→≃ n-Type-iso) (ua (prop-extₑ! f g) ,ₚ prop!)
    where instance _ = hlevel-prop-instance p
                   _ = hlevel-prop-instance q
  Extensional-Prop .idsᵉ .to-path-over {a = el _ p} _ = prop!
    where instance _ = hlevel-prop-instance p
  {-# OVERLAPPING Extensional-Prop #-}

opaque
  unfolding ua
  @0 n-univalence : {X Y : n-Type ℓ n} → (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ＝ Y)
  n-univalence {ℓ} {n} {X} {Y} = n-ua , is-inv→is-equiv (invertible inv (fun-ext rinv) (fun-ext (linv {Y}))) where
    inv : ∀ {Y} → X ＝ Y → ⌞ X ⌟ ≃ ⌞ Y ⌟
    inv p = =→≃ (ap carrier p)

    linv : {Y : n-Type ℓ n} → inv {Y} retract-of′ n-ua
    linv x = fun-ext (λ z → transport-refl _) ,ₚ prop!

    rinv : ∀ {Y} → (inv {Y}) section-of′ n-ua
    rinv = Jₚ (λ y p → n-ua (inv p) ＝ p) path where
      path : n-ua {X = X} (inv {X} refl) ＝ refl
      path i j .carrier = ua.ε refl i j
      path i j .carrier-is-tr = is-prop→squareᴾ
        (λ i j → is-of-hlevel-is-prop
          {A = ua.ε {A = ⌞ X ⌟} refl i j } n)
        (λ j → carrier-is-tr $ n-ua {X = X} {Y = X} (=→≃ refl) j)
        (λ _ → carrier-is-tr X)
        (λ _ → carrier-is-tr X)
        (λ _ → carrier-is-tr X)
        i j

-- FIXME disgusting! rewrite it without resorting to direct cube manipulations
opaque
  unfolding _∙ₚ_
  @0 n-path-∙ : {A B C : n-Type ℓ n}
                (p : ⌞ A ⌟ ＝ ⌞ B ⌟) (q : ⌞ B ⌟ ＝ ⌞ C ⌟)
              → n-path {X = A} {Y = C} (p ∙ q) ＝ n-path {Y = B} p ∙ n-path q
  n-path-∙ p q i j .carrier = (p ∙ q) j
  n-path-∙ {n} {A} {B} {C} p q j i .carrier-is-tr = θ i j where
    θ : Squareᴾ (λ k _ → is-of-hlevel n ((p ∙ q) k))
          refl (is-prop→pathᴾ (λ _ → is-of-hlevel-is-prop n) (A .carrier-is-tr) (C .carrier-is-tr))
          refl (λ k → (n-path {X = A} {Y = B} p ∙ n-path {Y = C} q) k .carrier-is-tr)
    θ = is-set→squareᴾ (λ _ _ → is-of-hlevel-is-of-hlevel-suc {h = n} 1) _ _ _ _

@0 n-ua-∙ₑ : {A B C : n-Type ℓ n}
             (f : ⌞ A ⌟ ≃ ⌞ B ⌟) (g : ⌞ B ⌟ ≃ ⌞ C ⌟)
           → n-ua {X = A} {Y = C} (f ∙ g) ＝ n-ua {Y = B} f ∙ n-ua g
n-ua-∙ₑ f g = ap n-path (ua-∙ₑ f g) ∙ n-path-∙ (ua f) (ua g)

opaque
  @0 n-Type-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
  n-Type-is-of-hlevel zero X Y = n-ua
    ((λ _ → carrier-is-tr Y .fst) , is-contr→is-equiv (X .carrier-is-tr) (Y .carrier-is-tr))
  n-Type-is-of-hlevel (suc n) X Y =
    ≃→is-of-hlevel (suc n) (n-univalence ⁻¹) (≃-is-of-hlevel (suc n) (X .carrier-is-tr) (Y .carrier-is-tr))


Prop : ∀ ℓ → Type (ℓsuc ℓ)
Prop ℓ = n-Type ℓ 1

Set : ∀ ℓ → Type (ℓsuc ℓ)
Set ℓ = n-Type ℓ 2

Grpd : ∀ ℓ → Type (ℓsuc ℓ)
Grpd ℓ = n-Type ℓ 3


-- Testing
-- module _ {ℓ : Level} {n : HLevel} where private
--   open import Foundations.Univalence.SIP
--   _ : n-Type ℓ n ≃ Type-with {S = is-of-hlevel n} (HomT→Str λ _ _ _ → ⊤)
--   _ = ≅→≃ n-Type-iso


-- n-truncated correspondence
n-Corr
  : (arity : ℕ) (n : HLevel) {ls : Levels arity} (As : Types arity ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup arity ls)
n-Corr arity n As ℓ = SCorr arity As (n-Type ℓ n)

n-Corr⁰ = n-Corr 0
n-Corr¹ = n-Corr 1
n-Corr² = n-Corr 2
n-Corr³ = n-Corr 3
n-Corr⁴ = n-Corr 4
n-Corr⁵ = n-Corr 5


-- Propositionally valued correspondence is called a relation
Rel
  : (arity : ℕ) {ls : Levels arity} (As : Types arity ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup arity ls)
Rel arity = n-Corr arity 1

Rel⁰ = Rel 0
Rel¹ = Rel 1
Rel² = Rel 2
Rel³ = Rel 3
Rel⁴ = Rel 4
Rel⁵ = Rel 5

n-Pred = n-Corr¹

Pred₀ = n-Pred 0
Pred₁ = n-Pred 1
Pred₂ = n-Pred 2
Pred₃ = n-Pred 3
Pred₄ = n-Pred 4
Pred₅ = n-Pred 5


-- Automation

el! : (A : Type ℓ) ⦃ A-hl : H-Level n A ⦄ → n-Type ℓ n
el! {n} A = el A (hlevel n)

opaque
  is-of-hlevel-≤ : ∀ n k → n ≤ʰ k → is-of-hlevel n A → is-of-hlevel k A
  is-of-hlevel-≤ 0 k 0≤x p = is-of-hlevel-+-left 0 k p
  is-of-hlevel-≤ 1 1 (s≤ʰs 0≤x) p = p
  is-of-hlevel-≤ 1 (suc (suc k)) (s≤ʰs 0≤x) p x y =
    is-of-hlevel-+-left 1 k (is-prop→is-set p x y)
  is-of-hlevel-≤ (suc (suc n)) (suc (suc k)) (s≤ʰs le) p x y =
    is-of-hlevel-≤ (suc n) (suc k) le (p x y)

private
  decompose-as-fixed-hlevel : Name → ℕ → Term → TC Term
  decompose-as-fixed-hlevel wnm lvl (def anm (_ ∷ ty ∷ [])) = do
    guard (wnm name=? anm)
    pure (lit (nat lvl))
  decompose-as-fixed-hlevel wnm _ t  = type-error
    [ "Target is not an application of " , name-err wnm , ": " , term-err t ]

  decompose-as-hlevel : Term → TC Term
  decompose-as-hlevel (def (quote is-of-hlevel) (_ ∷ varg lvl ∷ ty ∷ [])) =
    pure lvl
  decompose-as-hlevel t = type-error
    [ "Target is not an application of is-of-hlevel: " , term-err t ]

macro
  hlevel! : Term → TC ⊤
  hlevel! goal = with-reduce-defs (false ,
    [ it is-contr , it is-prop , it is-set , it is-of-hlevel ]) do
      ty ← infer-type goal >>= reduce
      let tel , ty′ = pi-view ty
      lvl ← decompose-as-fixed-hlevel (it is-contr) 0 ty′
        <|> decompose-as-fixed-hlevel (it is-prop)  1 ty′
        <|> decompose-as-fixed-hlevel (it is-set)   2 ty′
        <|> decompose-as-hlevel ty′
      unify goal (leave tel $ it hlevel ##ₙ lvl)

open Struct-proj-desc

instance
  hlevel-proj-n-type : Struct-proj-desc true (quote carrier)
  hlevel-proj-n-type .has-level = quote carrier-is-tr
  hlevel-proj-n-type .upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-n-type .get-level ty = do
    def (quote n-Type) (ℓ v∷ hl v∷ []) ← reduce ty
      where _ → type-error $ [ "Type of thing isn't n-Type, it is " , term-err ty ]
    normalise hl
  hlevel-proj-n-type .get-argument (_ ∷ _ ∷ x v∷ []) = pure x
  hlevel-proj-n-type .get-argument _ = type-error []

instance opaque
  @0 H-Level-n-Type : H-Level (suc n) (n-Type ℓ n)
  H-Level-n-Type {n} .H-Level.has-of-hlevel = n-Type-is-of-hlevel n
  {-# OVERLAPPING H-Level-n-Type #-}

  H-Level-projection
    : {A : Type ℓ} {n : ℕ}
    → {@(tactic struct-proj A (just n)) A-hl : is-of-hlevel n A}
    → H-Level n A
  H-Level-projection {A-hl} = hlevel-instance A-hl
  {-# OVERLAPS H-Level-projection #-}


-- Usage
private
  module _ {A : Set ℓ} {B : ⌞ A ⌟ → n-Type ℓ′ 3} where
    _ : is-set ⌞ A ⇒ A ⌟
    _ = hlevel!

    _ : is-of-hlevel 2 ⌞ A ⇒ A ⇒ A ⇒ A ⌟
    _ = hlevel!

    _ : is-of-hlevel 3 Σ[ B × B ]
    _ = hlevel!

    _ : ∀ a → is-of-hlevel 5 (⌞ A ⌟ × ⌞ A ⌟ × (ℕ ⇒ ⌞ B a ⌟))
    _ = hlevel!

    _ : ∀ a → is-of-hlevel 3 (⌞ A × A ⌟ × ℕ ⇒ ⌞ B a ⌟)
    _ = hlevel!

    _ : (w z : Term) (x : ℕ) (r : ⌞ A ⌟) → is-of-hlevel 2 ⌞ A ⌟
    _ = hlevel!

    _ : (a : ℕ) (x y : ⌞ A ⌟) → is-prop (x ＝ y)
    _ = hlevel!

    -- this one uses `H-Level-n-Type` instance which is compile-time only
    _ : Erased (∀ n → is-of-hlevel (suc n) (n-Type ℓ n))
    _ = erase hlevel!

    _ : is-of-hlevel 3 (Erased ⌞ A ⌟)
    _ = hlevel!

    _ : ∀ n (x : n-Type ℓ n) → is-of-hlevel (2 + n) ⌞ x ⌟
    _ = hlevel!

-- TODO restore
-- corr→is-of-hlevelⁿ
--   : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
--     {ℓ : Level} {h : HLevel} {P : n-Corr _ h As ℓ}
--   → Π[ mapⁿ arity (is-of-hlevel h) ⌞ P ⌟ ]
-- corr→is-of-hlevelⁿ {0} = hlevel!
-- corr→is-of-hlevelⁿ {1} = hlevel!
-- corr→is-of-hlevelⁿ {suc (suc arity)} _ = corr→is-of-hlevelⁿ {suc arity}
