{-# OPTIONS --safe #-}
module Data.AF.Prop where

open import Foundations.Base
open Variadics _
open import Meta.Effect.Map
open import Meta.Effect.Idiom

open import Data.Empty.Base
open import Data.Unit.Base
open import Data.Sum.Base
open import Data.AF.Base
open import Data.Truncation.Propositional as ∥-∥₁

data AF₁ {ℓ ℓ′} {A : 𝒰 ℓ} (R : A → A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  AF₁full : (∀ x y → ∥ R x y ∥₁) → AF₁ R
  AF₁lift : (∀ a → AF₁ (R ↑ a)) → AF₁ R
  AF₁squash : is-prop (AF₁ R)

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

af₁-inv : AF₁ R → ∀ {a} → AF₁ (R ↑ a)
af₁-inv (AF₁full f)         = AF₁full λ x y → map inl (f x y)
af₁-inv (AF₁lift l) {a}     = l a
af₁-inv (AF₁squash a₁ a₂ i) = AF₁squash (af₁-inv a₁) (af₁-inv a₂) i

af₁-mono : (∀ {x y} → R x y → T x y) -- TODO subseteq
        → AF₁ R → AF₁ T
af₁-mono sub (AF₁full f) =
  AF₁full λ x y → map sub (f x y)
af₁-mono sub (AF₁lift l) =
  AF₁lift λ a → af₁-mono (λ {x} {y} → ↑-mono sub {x} {y} {a}) (l a)
af₁-mono sub (AF₁squash a₁ a₂ i) = AF₁squash (af₁-mono sub a₁) (af₁-mono sub a₂) i

af₁-comap : ∀ {ℓa ℓb ℓr} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr}
         → (f : B → A)
         → AF₁ R → AF₁ (λ x y → R (f x) (f y))
af₁-comap f (AF₁full af)        = AF₁full λ x y → af (f x) (f y)
af₁-comap f (AF₁lift al)        = AF₁lift λ a → af₁-comap f (al (f a))
af₁-comap f (AF₁squash a₁ a₂ i) = AF₁squash (af₁-comap f a₁) (af₁-comap f a₂) i

af₁-map : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
           {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
       → {f : B → A} → (∀ x y → R (f x) (f y) → T x y)
       → AF₁ R → AF₁ T
af₁-map {f} fr (AF₁full af)        = AF₁full λ x y → map (fr x y) (af (f x) (f y))
af₁-map {f} fr (AF₁lift al)        = AF₁lift λ b → af₁-map (λ x y → [ inl ∘ fr x y , inr ∘ fr b x ]ᵤ) (al (f b))
af₁-map {f} fr (AF₁squash a₁ a₂ i) = AF₁squash (af₁-map fr a₁) (af₁-map fr a₂) i

af₁-rel-morph : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
              → (f : A → B → 𝒰 ℓ)
              → ((y : B) → ∃[ x ꞉ A ] (f x y))
              → ((x₁ x₂ : A) → (y₁ y₂ : B) → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
              → AF₁ R → AF₁ T
af₁-rel-morph f surj mor (AF₁full af) =
  AF₁full λ x y →
  (surj x) & ∥-∥₁.elim (λ _ → squash₁)
  λ where (a , fa) →
             (surj y) & ∥-∥₁.elim (λ _ → squash₁)
              λ where (b , fb) →
                         (af a b) & ∥-∥₁.elim (λ _ → squash₁)
                          λ r → ∣ mor a b x y fa fb r ∣₁
af₁-rel-morph f surj mor (AF₁lift al) =
  AF₁lift λ x →
  (surj x) & ∥-∥₁.elim (λ _ → AF₁squash)
  λ where (a , fa) →
            af₁-rel-morph f surj
              (λ x₁ x₂ y₁ y₂ f₁ f₂ → λ where
                                         (inl r₁₂) → inl (mor x₁ x₂ y₁ y₂ f₁ f₂ r₁₂)
                                         (inr ra₁) → inr (mor a  x₁ x  y₁ fa f₁ ra₁))
              (al a)
af₁-rel-morph f surj mor (AF₁squash a₁ a₂ i) =
  AF₁squash (af₁-rel-morph f surj mor a₁) (af₁-rel-morph f surj mor a₂) i
