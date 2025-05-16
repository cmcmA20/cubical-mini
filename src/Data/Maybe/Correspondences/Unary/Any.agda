{-# OPTIONS --safe --no-exact-split #-}
module Data.Maybe.Correspondences.Unary.Any where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Effect
open Variadics _
open import Foundations.Sigma

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Maybe.Operations
open import Data.Maybe.Instances.Map
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

data Any {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 Maybe A → 𝒰 (ℓᵃ ⊔ ℓ) where
  here  : (px : P x) → Any P (just x)

module _ {A : 𝒰 ℓᵃ} {P : Pred A ℓ} ⦃ ep : {a : A} → Extensional (P a) ℓ ⦄ where
  Code-Any : {xm : Maybe A} (p q : Any P xm) → 𝒰 ℓ
  Code-Any {xm = just x} (here px) (here qx) = ep .Pathᵉ px qx

  code-any-refl : {xm : Maybe A} (p : Any P xm) → Code-Any p p
  code-any-refl {xm = just x} (here px) = ep .reflᵉ px

  encode-any : {xm : Maybe A} {p q : Any P xm} → p ＝ q → Code-Any p q
  encode-any {p} e = subst (Code-Any p) e (code-any-refl p)

  decode-any : {xm : Maybe A} {p q : Any P xm} (c : Code-Any p q) → p ＝ q
  decode-any {xm = just x} {p = here px} {q = here qx} c = ap here (ep .idsᵉ .to-path c)

  decode-any-refl : {xm : Maybe A} {p q : Any P xm} (c : Code-Any p q)
                  → code-any-refl p ＝[ ap (Code-Any p) (decode-any c) ]＝ c
  decode-any-refl {xm = just x} {p = here px} {q = here qx} c = ep .idsᵉ .to-path-over c

  instance
    Extensional-Any : {xm : Maybe A} → Extensional (Any P xm) ℓ
    Extensional-Any      .Pathᵉ              = Code-Any
    Extensional-Any      .reflᵉ              = code-any-refl
    Extensional-Any      .idsᵉ .to-path      = decode-any
    Extensional-Any {xm} .idsᵉ .to-path-over = decode-any-refl {xm}

opaque
  -- TODO feels like it can be strengthened
  code-any-is-of-hlevel
    : ∀ {n} {xm : Maybe A} {u v : Any P xm}
    → (∀ x → is-of-hlevel (1 + n) (P x))
    → is-of-hlevel n (Code-Any u v)
  code-any-is-of-hlevel {n} {xm = just x} {u = here ux} {v = here vx} hl = path-is-of-hlevel n (hl x) ux vx

-- TODO how to add this to automation?
any-contr-is-prop :
    {xm : Maybe A}
  → (∀ x → is-contr (P x))
  → is-prop (Any P xm)
any-contr-is-prop {xm = just x} pc (here px) (here qx) =
  let (cx , ex) = pc x in
  ap here (ex px ⁻¹ ∙ ex qx)

-- TODO refactor?
any-is-of-hlevel
  : (n : HLevel) {xm : Maybe A}
  → (∀ x → is-of-hlevel (1 + n) (P x))
  → is-of-hlevel (1 + n) (Any P xm)
any-is-of-hlevel  zero   hl a1 a2 =
  ≃→is-of-hlevel 0
    (identity-system-gives-path (Extensional-Any .idsᵉ) ⁻¹)
    (code-any-is-of-hlevel {u = a1} hl)
    .fst
any-is-of-hlevel (suc n) hl a1 a2 =
  ≃→is-of-hlevel (suc n)
    (identity-system-gives-path (Extensional-Any .idsᵉ) ⁻¹)
    (code-any-is-of-hlevel {u = a1} hl)

instance opaque
  H-Level-Any : ∀ {n} {xm : Maybe A} → ⦃ n ≥ʰ 1 ⦄ → ⦃ A-hl : ∀ {x} → H-Level n (P x) ⦄ → H-Level n (Any P xm)
  H-Level-Any {n} ⦃ s≤ʰs _ ⦄ .H-Level.has-of-hlevel = any-is-of-hlevel _ (λ _ → hlevel n)
  {-# OVERLAPPING H-Level-Any #-}

here-inj : {p q : P x} → here {P = P} p ＝ here q → p ＝ q
here-inj {x} = encode-any {xm = just x}

instance
  Reflects-here=here
    : {xs : Maybe A} {p q : P x} ⦃ _ : Reflects (p ＝ q) b ⦄
    → Reflects (Path (Any P (just x)) (here p) (here q)) b
  Reflects-here=here {xs} = Reflects.dmap (ap here) (contra here-inj) auto

  ¬Any[] : Reflects (Any P nothing) false
  ¬Any[] = ofⁿ λ ()

unhere : Any P (just x) → P x
unhere (here px) = px

any-≃ : {x : A} → Any P (just x) ≃ P x
any-≃ =
  ≅→≃ $
  make-iso unhere here $
  make-inverses refl $
  fun-ext λ where
              (here px) → refl

any-map : {@0 xm : Maybe A} → ∀[ P ⇒ Q ] → Any P xm → Any Q xm
any-map f (here px) = here (f px)

any→map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xm : Maybe A}
        → Any (S ∘ f) xm → Any S (map f xm)
any→map (here px) = here px

any←map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xm : Maybe A}
        → Any S (map f xm) → Any (S ∘ f) xm
any←map {xm = just x} (here px) = here px

-- reflection

Reflects-any : {xm : Maybe A} {P : A → 𝒰 ℓ′} {p : A → Bool}
             → (∀ x → Reflects (P x) (p x))
             → Reflects (Any P xm) (any p xm)
Reflects-any {xm = just x}  rp = ≃→reflects (any-≃ ⁻¹) (rp x)
Reflects-any {xm = nothing} rp = ofⁿ false!

Reflects-any-bool : {p : A → Bool} {xm : Maybe A}
                  → Reflects (Any (So ∘ p) xm) (any p xm)
Reflects-any-bool = Reflects-any λ x → Reflects-So

Dec-any-bool : {p : A → Bool} {xm : Maybe A}
             → Dec (Any (So ∘ p) xm)
Dec-any-bool {p} {xm} .does  = any p xm
Dec-any-bool {p} {xm} .proof = Reflects-any-bool
