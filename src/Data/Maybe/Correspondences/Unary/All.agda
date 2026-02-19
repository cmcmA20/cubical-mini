{-# OPTIONS --safe #-}
module Data.Maybe.Correspondences.Unary.All where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Effect
open Variadics _
open import Foundations.Sigma

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Unit.Base
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Maybe.Operations
open import Data.Maybe.Instances.Map
open import Data.Maybe.Correspondences.Unary.Any
open import Data.Reflects.Base as Reflects
open import Data.Reflects.Properties

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  P Q R : Pred A ℓ
  S : Pred B ℓ′
  x : A
  @0 xm : Maybe A
  b : Bool

data All {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 Maybe A → 𝒰 (ℓᵃ ⊔ ℓ) where
  nothing : All P nothing
  just  : (px : P x) → All P (just x)

module _ {A : 𝒰 ℓᵃ} {P : Pred A ℓ} ⦃ ep : {a : A} → Extensional (P a) ℓ ⦄ where
  Code-All : {xm : Maybe A} (p q : All P xm) → 𝒰 ℓ
  Code-All {xm = just x} (just px) (just qx) = ep .Pathᵉ px qx
  Code-All {xm = nothing} nothing   nothing  = ⊤

  code-all-refl : {xm : Maybe A} (p : All P xm) → Code-All p p
  code-all-refl {xm = just x} (just px) = ep .reflᵉ px
  code-all-refl {xm = nothing} nothing  = lift tt

  decode-all : {xm : Maybe A} {p q : All P xm} (c : Code-All p q) → p ＝ q
  decode-all {xm = just x}  {p = just px} {q = just qx} c = ap just (ep .idsᵉ .to-path c)
  decode-all {xm = nothing} {p = nothing} {q = nothing} c = refl

  decode-all-refl : {xm : Maybe A} {p q : All P xm} (c : Code-All p q)
                  → code-all-refl p ＝[ ap (Code-All p) (decode-all c) ]＝ c
  decode-all-refl {xm = just x}  {p = just px} {q = just qx}  c        = ep .idsᵉ .to-path-over c
  decode-all-refl {xm = nothing} {p = nothing} {q = nothing} (lift tt) = refl

  -- TODO instance?
  Extensional-All : {xm : Maybe A} → Extensional (All P xm) ℓ
  Extensional-All .Pathᵉ                  = Code-All
  Extensional-All .reflᵉ                  = code-all-refl
  Extensional-All .idsᵉ .to-path          = decode-all
  Extensional-All .idsᵉ .to-path-over {a} = decode-all-refl {p = a}

opaque
  code-all-is-of-hlevel
    : ∀ {n} {xm : Maybe A} {u v : All P xm}
    → (∀ x → is-of-hlevel (suc n) (P x))
    → is-of-hlevel n (Code-All u v)
  code-all-is-of-hlevel {n = n} {xm = just x} {u = just px} {v = just qx} hl  =
    path-is-of-hlevel n (hl x) px qx
  code-all-is-of-hlevel {n = n} {xm = nothing} {u = nothing} {v = nothing} hl = hlevel n

all-is-contr
    : {xm : Maybe A}
    → (∀ x → is-contr (P x))
    → is-contr (All P xm)
all-is-contr {xm = just x} cntr =
  let (c , eq) = cntr x in
  (just c) , λ where (just qx) → ap just (eq qx)
all-is-contr {xm = nothing} cntr = nothing , λ where nothing → refl

all-is-of-hlevel
  : (n : HLevel) {xm : Maybe A}
  → (∀ x → is-of-hlevel n (P x))
  → is-of-hlevel n (All P xm)
all-is-of-hlevel  zero   hl = all-is-contr hl
all-is-of-hlevel (suc n) hl =
  identity-system→is-of-hlevel n (Extensional-All .idsᵉ) (λ x y → code-all-is-of-hlevel {u = x} hl)

instance
  H-Level-All : ∀ {n} {xm : Maybe A} → ⦃ A-hl : ∀ {x} → H-Level n (P x) ⦄ → H-Level n (All P xm)
  H-Level-All {n} .H-Level.has-of-hlevel = all-is-of-hlevel _ (λ _ → hlevel n)
  {-# OVERLAPPING H-Level-All #-}

all-unjust : All P (just x) → P x
all-unjust (just px) = px

all-just≃ : All P (just x) ≃ P x
all-just≃ =
  ≅→≃ $
  make-iso all-unjust just $
  make-inverses refl (fun-ext λ where (just px) → refl)

all-map : {@0 xm : Maybe A} → ∀[ P ⇒ Q ] → All P xm → All Q xm
all-map _  nothing  = nothing
all-map f (just px) = just (f px)

all→map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xm : Maybe A}
        → All (S ∘ f) xm → All S (map f xm)
all→map {xm = just x}  (just px) = just px
all→map {xm = nothing}  nothing  = nothing

all←map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xm : Maybe A}
        → All S (map f xm) → All (S ∘ f) xm
all←map {xm = just x}  (just px) = just px
all←map {xm = nothing}  nothing  = nothing

any→all : Any P xm → All P xm
any→all (here px) = just px

-- reflection

Reflects-all : {xm : Maybe A} {P : A → 𝒰 ℓ′} {p : A → Bool}
             → (∀ x → Reflects (P x) (p x))
             → Reflects (All P xm) (all p xm)
Reflects-all {xm = just x}  rp = ≃→reflects (all-just≃ ⁻¹) (rp x)
Reflects-all {xm = nothing} rp = ofʸ nothing

Dec-all : {P : A → 𝒰 ℓ′} {xm : Maybe A}
        → (∀ x → Dec (P x))
        → Dec (All P xm)
Dec-all {xm} d .does  = all (λ x → d x .does) xm
Dec-all      d .proof = Reflects-all λ x → d x .proof

Reflects-all-bool : {p : A → Bool} {xm : Maybe A}
                  → Reflects (All (So ∘ p) xm) (all p xm)
Reflects-all-bool = Reflects-all λ x → Reflects-So

Dec-all-bool : ∀ {p : A → Bool} {xm : Maybe A}
             → Dec (All (So ∘ p) xm)
Dec-all-bool {p} {xm} .does  = all p xm
Dec-all-bool          .proof = Reflects-all-bool
