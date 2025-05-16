{-# OPTIONS --safe --no-exact-split #-}
module Data.Maybe.Membership where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Effect

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Maybe.Operations
open import Data.Maybe.Instances.Map
open import Data.Maybe.Correspondences.Unary.Any

open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

private variable
  ℓᵃ ℓ : Level
  A : Type ℓᵃ
  a x y : A
  xm : Maybe A

_∈ₘ_ : ∀ {ℓᵃ} {A : Type ℓᵃ}
     → A → Maybe A → Type ℓᵃ
x ∈ₘ xm = Any (x ＝_) xm

instance
  Membership-Maybe : {A : Type ℓ} → Membership A (Maybe A) ℓ
  Membership-Maybe ._∈_ = _∈ₘ_

instance
  ∈ₘ-just : Reflects (x ∈ₘ just x) true
  ∈ₘ-just = ofʸ (here refl)
  {-# OVERLAPPING ∈ₘ-just #-}

has : ⦃ d : is-discrete A ⦄ → A → Maybe A → Bool
has a = any (λ x → ⌊ a ≟ x ⌋)

Reflects-has : ⦃ d : is-discrete A ⦄ {x : A} {xm : Maybe A}
             → Reflects (x ∈ xm) (has x xm)
Reflects-has ⦃ d ⦄ {x} = Reflects-any λ y → d {x} {y} .proof

instance
  Dec-∈ₘ
    : {a : A} {xm : Maybe A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈ xm)
  Dec-∈ₘ {a} {xm} .does = has a xm
  Dec-∈ₘ          .proof = Reflects-has
  {-# OVERLAPPING Dec-∈ₘ #-}

¬here→∉ : a ≠ x → a ∉ just x
¬here→∉ ne (here px) = ne px

∈-map : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xm : Maybe A}
       → (f : A → B) → x ∈ xm → f x ∈ map f xm
∈-map {xm = just x} f (here e) = here (ap f e)

map-∈ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xm : Maybe A}
       → (f : A → B) → Injective f
       → f x ∈ map f xm → x ∈ xm
map-∈ {xm = just x} f inj (here e) = here (inj e)

map-∈Σ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {y : B} {xm : Maybe A}
        → (f : A → B)
        → y ∈ map f xm → Σ[ x ꞉ A ] ((x ∈ xm) × (y ＝ f x))
map-∈Σ {xm = just x} f (here e) = x , here refl , e

Any→Σ∈ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm : Maybe A}
         → Any P xm
         → Σ[ x ꞉ A ] x ∈ xm × P x
Any→Σ∈ {xm = just x} (here px) = x , here refl , px

∈→Any : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm : Maybe A} {x : A}
       → x ∈ xm → P x
       → Any P xm
∈→Any {P} {xm = just y} (here e) px = here (subst P e px)

any-⊆ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm ym : Maybe A}
       → xm ⊆ ym → Any P xm → Any P ym
any-⊆ xsy ax =
  let (x , x∈ , px) = Any→Σ∈ ax in
  ∈→Any (xsy x∈) px
