{-# OPTIONS --safe #-}
module Data.AF.Base where

open import Foundations.Base
open Variadics _
open import Meta.Effect.Map
open import Meta.Effect.Idiom

open import Data.Empty.Base
open import Data.Unit.Base
open import Data.Sum.Base

open import Data.List.Base
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership

_↑_ : ∀ {ℓ ℓ′} {A : 𝒰 ℓ} → (A → A → 𝒰 ℓ′) → A → A → A → 𝒰 ℓ′
(R ↑ a) x y = R x y ⊎ R a x

data AF {ℓ ℓ′} {A : 𝒰 ℓ} (R : A → A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  AFfull : (∀ x y → R x y) → AF R
  AFlift : (∀ a → AF (R ↑ a)) → AF R

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

↑-mono : (∀ {x y} → R x y → T x y) -- TODO subseteq
       → ∀ {x y a} → (R ↑ a) x y → (T ↑ a) x y
↑-mono sub = dmap sub sub

-- list lifting
_↑↑_ : (A → A → 𝒰 ℓ′) → List A
     → A → A → 𝒰 ℓ′
R ↑↑ []      = R
R ↑↑ (a ∷ l) = (R ↑↑ l) ↑ a

↑↑-inc : {R : A → A → 𝒰 ℓ′} (l : List A)
       → ∀ {x y} → R x y → (R ↑↑ l) x y -- TODO subseteq
↑↑-inc []      rxy = rxy
↑↑-inc (h ∷ l) rxy = inl $ ↑↑-inc l rxy

↑↑-mono : (∀ {x y} → R x y → T x y) -- TODO subseteq
        → ∀ {x y} l → (R ↑↑ l) x y → (T ↑↑ l) x y
↑↑-mono sub []       rlxy      = sub rlxy
↑↑-mono sub (a ∷ l) (inl rlxy) = inl $ ↑↑-mono sub l rlxy
↑↑-mono sub (a ∷ l) (inr rlax) = inr $ ↑↑-mono sub l rlax

↑↑-∈ : ∀ {x y} l → R y x → y ∈ l → ∀ z → (R ↑↑ l) x z
↑↑-∈ {R} {x} (a ∷ l) ryx (here e)   z = inr $ ↑↑-inc l $ subst (λ q → R q x) e ryx
↑↑-∈         (a ∷ l) ryx (there yl) z = inl $ ↑↑-∈ l ryx yl z

-- AF properties

af-inv : AF R → ∀ {a} → AF (R ↑ a)
af-inv (AFfull f)     = AFfull λ x y → inl (f x y)
af-inv (AFlift l) {a} = l a

af-mono : (∀ {x y} → R x y → T x y) -- TODO subseteq
        → AF R → AF T
af-mono sub (AFfull f) =
  AFfull λ x y → sub (f x y)
af-mono sub (AFlift l) =
  AFlift λ a → af-mono (λ {x} {y} → ↑-mono sub {x} {y} {a}) (l a)

af-comap : ∀ {ℓa ℓb ℓr} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr}
         → (f : B → A)
         → AF R → AF (λ x y → R (f x) (f y))
af-comap f (AFfull af) = AFfull λ x y → af (f x) (f y)
af-comap f (AFlift al) = AFlift λ a → af-comap f (al (f a))

af-map : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
           {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
       → {f : B → A} → (∀ x y → R (f x) (f y) → T x y)
       → AF R → AF T
af-map {f} fr (AFfull af) = AFfull λ x y → fr x y (af (f x) (f y))
af-map {f} fr (AFlift al) = AFlift λ b → af-map (λ x y → dmap (fr x y) (fr b x)) (al (f b))

-- surjective relational morphism

af-rel-morph : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
             → (f : A → B → 𝒰 ℓ)
             → ((y : B) → Σ[ x ꞉ A ] (f x y))
             → ((x₁ x₂ : A) → (y₁ y₂ : B) → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
             → AF R → AF T
af-rel-morph f surj mor (AFfull af) =
  AFfull λ x y →
  let (a , fa) = surj x
      (b , fb) = surj y
    in
  mor a b x y fa fb (af a b)
af-rel-morph f surj mor (AFlift al) =
  AFlift λ x →
  let (a , fa) = surj x in
  af-rel-morph f surj
    (λ x₁ x₂ y₁ y₂ f₁ f₂ → dmap (mor x₁ x₂ y₁ y₂ f₁ f₂)
                                (mor a  x₁ x  y₁ fa f₁))
    (al a)

-- derived versions

af-mono′ : (∀ {x y} → R x y → T x y)
         → AF R → AF T
af-mono′ {T} f =
  af-rel-morph _＝_ (λ y → y , refl)
  λ x₁ x₂ y₁ y₂ e₁ e₂ → subst (λ q → T q y₂) e₁ ∘ subst (T x₁) e₂ ∘ f

af-comap′ : ∀ {ℓa ℓb ℓr} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr}
          → (f : B → A)
          → AF R → AF (λ x y → R (f x) (f y))
af-comap′ {R} f =
  af-rel-morph (λ x y → x ＝ f y) (λ y → f y , refl)
    λ x₁ x₂ y₁ y₂ e₁ e₂ → subst (λ q → R q (f y₂)) e₁ ∘ subst (R x₁) e₂

af-map′ : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
            {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
        → {f : B → A} → (∀ x y → R (f x) (f y) → T x y)
        → AF R → AF T
af-map′ {R} {f} fr =
  af-rel-morph (λ x y → x ＝ f y) (λ y → f y , refl)
    λ x₁ x₂ y₁ y₂ e₁ e₂ → fr y₁ y₂ ∘ subst (λ q → R q (f y₂)) e₁ ∘ subst (R x₁) e₂
