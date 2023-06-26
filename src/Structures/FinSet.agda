{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base
open import Foundations.Sigma

open import Meta.Idiom
open import Meta.Decision
open import Meta.HLevel
open import Meta.Finite     public
open import Meta.Underlying public

open import Structures.n-Type

open import Correspondences.Nullary.Omniscience
open import Correspondences.Unary.Decidable

import      Data.Dec.Base as Dec
open Dec
open import Data.Dec.Properties
open import Data.Dec.Instances.HLevel
open import Data.Empty
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Data.Vec.Correspondences.Unary.Any

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Fin-ordered : Type ℓ → Type ℓ
Fin-ordered A = Σ[ n ꞉ ℕ ] (A ≃ Fin n)

fin-ordered-is-set : is-set (Fin-ordered A)
fin-ordered-is-set = hlevel!

is-fin-set : Type ℓ → Type ℓ
is-fin-set A = Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁

-- FIXME
-- is-fin-set-is-prop : is-prop (is-fin-set A)
-- is-fin-set-is-prop (m , ∣p∣₁) (n , ∣q∣₁) =
--   Σ-prop-path-equiv hlevel! .fst $
--     ∥-∥₁.elim₂ (λ _ _ → ℕ-is-set m n)
--                (λ p q → fin-injective ((p ₑ⁻¹) ∙ₑ q))
--                ∣p∣₁
--                ∣q∣₁

Finite→is-fin-set : Finite A → is-fin-set A
Finite→is-fin-set A-fin = A-fin .cardinality , A-fin .enumeration

is-fin-set→is-set : is-fin-set A → is-set A
is-fin-set→is-set (_ , ∣e∣₁) =
  ∥-∥₁.rec (is-of-hlevel-is-prop 2) (λ e → is-of-hlevel-≃ 2 e hlevel!) ∣e∣₁

fin-ordered→is-fin-set : Fin-ordered A → is-fin-set A
fin-ordered→is-fin-set (n , e) = n , ∣ e ∣₁

-- TODO
-- fin-set→is-discrete : is-fin-set A → is-discrete A
-- fin-set→is-discrete A-f = {!!}

fin-ordered→omniscient : Fin-ordered A → Omniscient {ℓ′ = ℓ′} A
fin-ordered→omniscient {A} (n , aeq) {P} P? =
  Dec.map lemma₁ lemma₂ (any? P? xs) where
    module Ã = Equiv aeq
    module Ṽ = Equiv vec-fun-equiv

    xs : Vec A n
    xs = Ṽ.inverse .fst $ Ã.inverse .fst

    lemma₁ : _
    lemma₁ (i , p) = lookup xs i , p

    lemma₂ : _
    lemma₂ ¬p (a , pa) = ¬p $ Ã.to a , subst P (sym (happly (Ṽ.ε _) _ ∙ Ã.η a)) pa

is-fin-set→omniscient₁ : is-fin-set A → Omniscient₁ {ℓ′ = ℓ′} A
is-fin-set→omniscient₁ {A} (n , ∣aeq∣₁) {P} = ∥-∥₁.elim! go ((n ,_) <$> ∣aeq∣₁) where
  go : Π[ A-f ꞉ Fin-ordered A ] (Decidable₁ P → Dec ∥ Σ A _ ∥₁)
  go A-f = Dec.map pure rec! ∘ fin-ordered→omniscient A-f

is-fin-set→exhaustible₁ : is-fin-set A → Exhaustible₁ {ℓ′ = ℓ′} A
is-fin-set→exhaustible₁ = omniscient₁→exhaustible₁ ∘ is-fin-set→omniscient₁

-- is-fin-set→omniscient
--   : is-fin-set A → {P : Pred₁ ℓ′ A} → Decidable₁ P → Dec (Σ[ a ꞉ A ] ⌞ P a ⌟)
-- is-fin-set→omniscient A-fin P? with is-fin-set→omniscient₁ A-fin P?
-- ... | yes p = yes {!!}
-- ... | no ¬p = {!!}

-- is-fin-set→exhaustible₁
--   : is-fin-set A → {P : Pred₁ ℓ′ A} → Decidable₁ P → Dec (Π[ a ꞉ A ] ⌞ P a ⌟)
-- is-fin-set→exhaustible₁ A-fin {P} P? =
--   let z = omniscient₁→exhaustible₁ (is-fin-set→omniscient₁ A-fin) P?
-- --       w = ∥-∥₁.proj (Finite-choice ⦃ {!!} ⦄ λ x → (dec-∥-∥₁-equiv ₑ⁻¹) .fst x)
--   in omniscient→exhaustible {!!} P?
-- --     in ∥-∥₁.proj {!Finite-choice ? ?!} -- ((dec-∥-∥₁-equiv ₑ⁻¹) .fst z)

record FinSet ℓ : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-set
  field
    typ            : Type ℓ
    has-is-fin-set : is-fin-set typ
  instance
    Finite-FinSet : Finite typ
    Finite-FinSet = fin $ has-is-fin-set .snd

    -- H-Level-FinSet : ∀ {n} → HLevel (2 + n) typ
    -- H-Level-FinSet = basic-instance 2 (is-fin-set→is-set has-is-fin-set)

-- open FinSet public
--   using (Finite-FinSet; H-Level-FinSet)
open FinSet using (typ; has-is-fin-set)

fin-set! : (A : Type ℓ) → ⦃ Finite A ⦄ → FinSet ℓ
fin-set! A ⦃ (A-fin) ⦄ = fin-set A (Finite→is-fin-set A-fin)

instance
  Underlying-FinSet : Underlying (FinSet ℓ)
  Underlying-FinSet {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinSet .⌞_⌟ = typ


-- TODO
-- fin-set-path : ⌞ X ⌟ ＝ ⌞ Y ⌟ → X ＝ Y
-- fin-set-path f i .typ = f i
-- fin-set-path {X} {Y} f i .has-is-fin-set = {!!} , {!!}
--   -- is-prop→pathP (λ i → is-of-hlevel-is-prop {A = f i} _) (X .is-tr) (Y .is-tr) i

-- @0 fin-set-ua : ⌞ X ⌟ ≃ ⌞ Y ⌟ → X ＝ Y
-- fin-set-ua f = n-path (ua f)

-- @0 fin-set-univalence : {X Y : n-Type ℓ n} → (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ＝ Y)
-- fin-set-univalence {n} {X} {Y} = n-ua , is-iso→is-equiv isic where
--   inv : ∀ {Y} → X ＝ Y → ⌞ X ⌟ ≃ ⌞ Y ⌟
--   inv p = path→equiv (ap typ p)

--   linv : ∀ {Y} → (inv {Y}) is-left-inverse-of n-ua
--   linv x = Σ-prop-path is-equiv-is-prop (fun-ext λ x → transport-refl _)

--   rinv : ∀ {Y} → (inv {Y}) is-right-inverse-of n-ua
--   rinv = J (λ y p → n-ua (inv p) ＝ p) path where
--     path : n-ua (inv {X} refl) ＝ refl
--     path i j .typ = ua.ε refl i j
--     path i j .is-tr = is-prop→SquareP
--       (λ i j → is-of-hlevel-is-prop
--         {A = ua.ε {A = ⌞ X ⌟} refl i j } n)
--       (λ j → X .is-tr) (λ j → n-ua {X = X} {Y = X} (path→equiv refl) j .is-tr)
--       (λ j → X .is-tr) (λ j → X .is-tr)
--       i j

--   isic : is-iso n-ua
--   isic = iso inv rinv (linv {Y})

-- @0 fin-set-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
-- fin-set-is-of-hlevel zero x y = n-ua
--   ((λ _ → y .is-tr .fst) , is-contr→is-equiv (x .is-tr) (y .is-tr))
-- fin-set-is-of-hlevel (suc n) x y =
--   is-of-hlevel-≃ (suc n) (n-univalence ₑ⁻¹) (≃-is-of-hlevel (suc n) (x .is-tr) (y .is-tr))

-- instance
--   @0 H-Level-nType : ∀ {n k} → H-Level (1 + k + n) (n-Type ℓ k)
--   H-Level-nType {k} = basic-instance (1 + k) (n-Type-is-of-hlevel k)

--   H-Level-is-equiv
--     : {f : A → B} {n : HLevel}
--     → H-Level (suc n) (is-equiv f)
--   H-Level-is-equiv = prop-instance (is-equiv-is-prop _)

-- module _ {ℓ : Level} where private
--   open import Foundations.Univalence.SIP
--   _ : FinSet ℓ ≃ Type-with {S = is-fin-set} (HomT→Str λ _ _ _ → ⊤)
--   _ = iso→equiv the-iso
--     where
--       open import Meta.Reflection.Record
--       the-iso : Iso (FinSet ℓ) (Σ[ T ꞉ Type ℓ ] is-fin-set T)
--       unquoteDef the-iso = define-record-iso the-iso (quote FinSet)
