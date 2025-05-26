{-# OPTIONS --safe #-}
module Data.AF.Prop where

open import Meta.Prelude
open import Meta.Effect
open Variadics _

open import Data.Empty.Base
open import Data.Unit.Base
open import Data.Sum.Base
open import Data.AF.Base
open import Data.Truncation.Propositional as ∥-∥₁

_↑₁_ : ∀ {ℓ ℓ′} {A : 𝒰 ℓ} → (A → A → 𝒰 ℓ′) → A → A → A → 𝒰 ℓ′
(R ↑₁ a) x y = R x y ⊎₁ R a x

-- TODO R : A → A → Prop ℓ′ ?
data AF₁ {ℓ ℓ′} {A : 𝒰 ℓ} (R : A → A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  AF₁full   : (∀ x y → ∥ R x y ∥₁) → AF₁ R
  AF₁lift   : (∀ a → AF₁ (R ↑₁ a)) → AF₁ R
  AF₁squash : is-prop (AF₁ R)

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

↑₁-mono : (∀ {x y} → R x y → T x y) -- TODO subseteq
        → ∀ {x y a} → (R ↑₁ a) x y → (T ↑₁ a) x y
↑₁-mono sub = map (dmap sub sub)

instance opaque
  H-Level-AF₁ : ∀ {n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (AF₁ R)
  H-Level-AF₁ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance AF₁squash
  {-# OVERLAPPING H-Level-AF₁ #-}

af₁-inv : AF₁ R → ∀ {a} → AF₁ (R ↑₁ a)
af₁-inv (AF₁full f)         = AF₁full λ x y → ∣ map inl (f x y) ∣₁
af₁-inv (AF₁lift l) {a}     = l a
af₁-inv (AF₁squash a₁ a₂ i) = AF₁squash (af₁-inv a₁) (af₁-inv a₂) i

af₁-mono : (∀ {x y} → R x y → T x y) -- TODO subseteq
         → AF₁ R → AF₁ T
af₁-mono sub (AF₁full f) =
  AF₁full λ x y → map sub (f x y)
af₁-mono sub (AF₁lift l) =
  AF₁lift λ a → af₁-mono (λ {x} {y} → ↑₁-mono sub {x} {y} {a})
                         (l a)
af₁-mono sub (AF₁squash a₁ a₂ i) =
  AF₁squash (af₁-mono sub a₁) (af₁-mono sub a₂) i

af₁-comap : ∀ {ℓa ℓb ℓr} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr}
          → (f : B → A)
          → AF₁ R → AF₁ (λ x y → R (f x) (f y))
af₁-comap f (AF₁full af)        =
  AF₁full λ x y → af (f x) (f y)
af₁-comap f (AF₁lift al)        =
  AF₁lift λ a → af₁-comap f (al (f a))
af₁-comap f (AF₁squash a₁ a₂ i) =
  AF₁squash (af₁-comap f a₁) (af₁-comap f a₂) i

af₁-map : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
            {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
        → {f : B → A} → (∀ x y → R (f x) (f y) → T x y)
        → AF₁ R → AF₁ T
af₁-map {f} fr (AF₁full af)        =
  AF₁full λ x y → map (fr x y) (af (f x) (f y))
af₁-map {f} fr (AF₁lift al)        =
  AF₁lift λ b → af₁-map (λ x y → map (dmap (fr x y) (fr b x))) (al (f b))
af₁-map {f} fr (AF₁squash a₁ a₂ i) =
  AF₁squash (af₁-map fr a₁) (af₁-map fr a₂) i

af₁-rel-morph : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
                  {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
              → (f : A → B → 𝒰 ℓ)
              → ((y : B) → ∃[ x ꞉ A ] (f x y))
              → ((x₁ x₂ : A) → (y₁ y₂ : B) → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
              → AF₁ R → AF₁ T
af₁-rel-morph f surj mor (AF₁full af) =
  AF₁full λ x y →
  (surj x) & elim! λ a fa →
  (surj y) & elim! λ b fb →
  map (mor a b x y fa fb) (af a b)
af₁-rel-morph f surj mor (AF₁lift al) =
  AF₁lift λ x →
  (surj x) & elim! λ a fa →
  af₁-rel-morph f surj
    (λ x₁ x₂ y₁ y₂ f₁ f₂ → map (dmap (mor x₁ x₂ y₁ y₂ f₁ f₂)
                                     (mor a  x₁ x  y₁ fa f₁)))
    (al a)
af₁-rel-morph f surj mor (AF₁squash a₁ a₂ i) =
  AF₁squash (af₁-rel-morph f surj mor a₁) (af₁-rel-morph f surj mor a₂) i

-- derived versions

af₁-mono′ : (∀ {x y} → R x y → T x y)
          → AF₁ R → AF₁ T
af₁-mono′ {T} f =
  af₁-rel-morph _＝_ (λ y → ∣ y , refl ∣₁)
    λ x₁ x₂ y₁ y₂ e₁ e₂ → subst (λ q → T q y₂) e₁ ∘ subst (T x₁) e₂ ∘ f

af₁-comap′ : ∀ {ℓa ℓb ℓr} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr}
           → (f : B → A)
           → AF₁ R → AF₁ (λ x y → R (f x) (f y))
af₁-comap′ {R} f =
  af₁-rel-morph (λ x y → x ＝ f y) (λ y → ∣ f y , refl ∣₁)
    λ x₁ x₂ y₁ y₂ e₁ e₂ → subst (λ q → R q (f y₂)) e₁ ∘ subst (R x₁) e₂

af₁-map′ : ∀ {ℓa ℓb ℓr ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
             {R : A → A → 𝒰 ℓr} {T : B → B → 𝒰 ℓt}
         → {f : B → A} → (∀ x y → R (f x) (f y) → T x y)
         → AF₁ R → AF₁ T
af₁-map′ {R} {f} fr =
  af₁-rel-morph (λ x y → x ＝ f y) (λ y → ∣ f y , refl ∣₁)
    λ x₁ x₂ y₁ y₂ e₁ e₂ → fr y₁ y₂ ∘ subst (λ q → R q (f y₂)) e₁ ∘ subst (R x₁) e₂
