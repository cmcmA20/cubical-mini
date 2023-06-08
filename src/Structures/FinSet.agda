{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma

open import Data.Fin
import      Data.Empty
import      Data.Dec.Base as Dec
open import Data.Dec.Properties
open import Data.Dec.Instances.HLevel
open import Data.Vec.Base
open import Data.Vec.Correspondences.Unary.Any
open import Data.Vec.Correspondences.Unary.All
open import Data.Vec.Membership
open import Data.Nat.Path
open import Data.Nat.Instances.Discrete
open import Data.Vec.Properties

open import Meta.Idiom
open import Meta.Discrete
open import Meta.Reflection.HLevel
open import Meta.Finite            public
open import Meta.Underlying        public

open import Correspondences.Unary.Decidable

open import Structures.Negation
open import Structures.Omniscience

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

Fin-ordered : Type ℓ → Type ℓ
Fin-ordered A = Σ[ n ꞉ ℕ ] A ≃ Fin n

fin-ordered-is-set : is-set (Fin-ordered A)
fin-ordered-is-set =
  Σ-is-of-hlevel 2 hlevel! (λ _ → ≃-is-of-hlevel-right-suc 1 hlevel!)

is-fin-set : Type ℓ → Type ℓ
is-fin-set A = Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁

is-fin-set-is-prop : is-prop (is-fin-set A)
is-fin-set-is-prop (m , ∣p∣₁) (n , ∣q∣₁) =
  Σ-prop-path-equiv hlevel! .fst $
    ∥-∥₁.elim₂ (λ _ _ → ℕ-is-set m n)
               (λ p q → fin-injective ((p ₑ⁻¹) ∙ₑ q))
               ∣p∣₁
               ∣q∣₁

is-fin-set→is-set : is-fin-set A → is-set A
is-fin-set→is-set (_ , ∣e∣₁) =
  ∥-∥₁.rec (is-of-hlevel-is-prop 2) (λ e → is-of-hlevel-≃ 2 e hlevel!) ∣e∣₁

fin-ordered→is-fin-set : Fin-ordered A → is-fin-set A
fin-ordered→is-fin-set (n , e) = n , ∣ e ∣₁

-- TODO
-- fin-set→is-discrete : is-fin-set A → is-discrete A
-- fin-set→is-discrete A-f = {!!}

dec-∥-∥₁-equiv : ∥ Dec A ∥₁ ≃ Dec ∥ A ∥₁
dec-∥-∥₁-equiv = prop-extₑ!
  (∥-∥₁.rec! $ Dec.map pure ∥-∥₁.rec!)
  (Dec.rec (yes <$>_) $ pure ∘ no ∘ _∘ pure)

fin-ordered→omniscient : Fin-ordered A → Omniscient {ℓ′ = ℓ′} A
fin-ordered→omniscient {A} (n , aeq) {P} P? =
  Dec.map lemma₁ lemma₂ (any′? P? xs) where
    module Â = Equiv aeq
    module V̂ = Equiv vec-fun-equiv

    xs : Vec A n
    xs = V̂.inverse .fst $ Â.inverse .fst

    lemma₁ : _
    lemma₁ (i , p) = lookup xs i , p

    lemma₂ : _
    lemma₂ ¬p (a , pa) = ¬p $ Â.to a , subst P (sym (happly (V̂.ε _) _ ∙ Â.η a)) pa

is-fin-set→omniscient₁ : is-fin-set A → Omniscient₁ {ℓ′ = ℓ′} A
is-fin-set→omniscient₁ {A} (n , ∣aeq∣₁) {P} = ∥-∥₁.elim! go ((n ,_) <$> ∣aeq∣₁) where
    go : Π[ a ꞉ Fin-ordered A ] (Decidable P → Dec ∥ Σ A P ∥₁)
    go A-f = Dec.map pure rec! ∘ fin-ordered→omniscient A-f

record FinSet ℓ : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-set
  field
    typ            : Type ℓ
    has-is-fin-set : is-fin-set typ
  instance
    Finite-FinSet : Finite typ
    Finite-FinSet = fin $ has-is-fin-set .snd

    H-Level-FinSet : ∀ {n} → H-Level (2 + n) typ
    H-Level-FinSet = basic-instance 2 (is-fin-set→is-set has-is-fin-set)

open FinSet public
  using (Finite-FinSet; H-Level-FinSet)
open FinSet using (typ; has-is-fin-set)

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
