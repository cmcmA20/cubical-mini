{-# OPTIONS --safe #-}
module Data.Reflects.Sigma where

open import Foundations.Prelude
open import Meta.Effect

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Unit.Base as ⊤
open import Data.Sum as Sum hiding (dmap)
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any

open import Data.Reflects.Base hiding (dmap)

-- `ReflectsΣ P m` = m is a potential solution to the function problem described by P
data ReflectsΣ {ℓ ℓ′} {A : 𝒰 ℓ} (P : A → 𝒰 ℓ′) : Maybe A → 𝒰 (ℓ ⊔ ℓ′) where
  ofʲ : (x : A) → P x → ReflectsΣ P (just x)
  ofⁿ : (∀ x → ¬ P x) → ReflectsΣ P nothing

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  P : A → Type ℓ′
  Q : A → Type ℓ″
  m : Maybe A

dmap : (∀ x → P x → Q x)
     → (∀ x → ¬ (P x) → ¬ (Q x)) -- is this general enough?
     → ReflectsΣ P m → ReflectsΣ Q m
dmap to fro (ofʲ x px) = ofʲ x (to x px)
dmap to fro (ofⁿ nx)   = ofⁿ λ x → fro x (nx x)

reflectsΣ-∈ : {m : Maybe A} → ReflectsΣ (_∈ₘ m) m
reflectsΣ-∈ {m = just x}  = ofʲ x (here refl)
reflectsΣ-∈ {m = nothing} = ofⁿ λ x → false!

-- combinators

reflectsΣ-map : {A : Type ℓᵃ} {B : Type ℓᵇ}
                {P : A → Type ℓ′} {Q : B → Type ℓ″}
                {m : Maybe A} {f : A → B}
                (g : B → A)
              → (∀ x → P x → Q (f x))
              → (∀ y → ¬ P (g y) → ¬ Q y)
              -- + some condition on f cancelling g ?
              → ReflectsΣ P m
              → ReflectsΣ Q (mapₘ f m)
reflectsΣ-map {f} _ pq npq (ofʲ x px) = ofʲ (f x) (pq x px)
reflectsΣ-map     g pq npq (ofⁿ nx)   = ofⁿ λ y → npq y (nx (g y))

{-
reflectsΣ-bind : {A : Type ℓᵃ} {B : Type ℓᵇ}
                {P : A → Type ℓ′} {Q R : B → Type ℓ″}
                {m : Maybe A} {f : A → Maybe B}
                (g : B → A)
              → (∀ y → ¬ P (g y) → ¬ Q y)
              → ReflectsΣ P m
              → (∀ a → ReflectsΣ Q (f a))
              → ReflectsΣ R (bindₘ m f)
reflectsΣ-bind g npq (ofʲ x px) rf = {!!} -- rf x
reflectsΣ-bind g npq (ofⁿ nx)   rf = ofⁿ λ y → {!!} -- npq y (nx (g y))
-}

reflectsΣ-alter : {A : Type ℓᵃ} {B : Type ℓᵇ}
                  {P : A → Type ℓ′} {Q : B → Type ℓ′}
                  {ma : Maybe A} {mb : Maybe B}
                → ReflectsΣ P ma
                → ReflectsΣ Q mb
                → ReflectsΣ [ P , Q ]ᵤ (ma <+> mb)
reflectsΣ-alter (ofʲ x px)  rb        = ofʲ (inl x) px
reflectsΣ-alter (ofⁿ nx)   (ofʲ y qy) = ofʲ (inr y) qy
reflectsΣ-alter (ofⁿ nx)   (ofⁿ ny)   = ofⁿ (Sum.elim nx ny)

-- mapping

ReflectsΣ→Reflects : {A : Type ℓᵃ} {P : A → Type ℓ′} {m : Maybe A} {x : A}
                   → ReflectsΣ P m → Reflects (Any P m) (Maybe.is-just? m)
ReflectsΣ→Reflects (ofʲ x px) = ofʸ (here px)
ReflectsΣ→Reflects (ofⁿ nx) = ofⁿ false!

∈→true : {A : Type ℓᵃ} {P : A → Type ℓ′} {m : Maybe A} {x : A}
       → ReflectsΣ P m → x ∈ m → P x
∈→true {P} (ofʲ x px) (here e) = subst P (e ⁻¹) px

-- the other way requires (∀ {x y} → P x → P y → x ＝ y)
