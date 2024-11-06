{-# OPTIONS --safe #-}
module Data.AF.Constructions where

open import Foundations.Base
open import Foundations.HLevel
open Variadics _

open import Data.Empty.Base
open import Data.Unit.Base
open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Reflects.Base
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Maybe.Base
open import Data.Nat
open import Data.Nat.Order.Base
--open import Data.Fin.Computational.Base

open import Data.AF.Base
open import Data.AF.Ramsey
open import Data.AF.WF

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

af-unit : AF {A = A} (λ _ _ → Lift ℓ′ ⊤)
af-unit = AFfull λ _ _ → lift tt

af-⊤ : AF {A = ⊤} _＝_
af-⊤ = AFfull (hlevel 1)

af-bool : AF {A = Bool} _＝_
af-bool =
  AFlift λ a → AFlift λ b → AFlift λ c → AFfull λ x y →
  Bool.elim {P = λ q → (((_＝_ ↑ q) ↑ b) ↑ c) x y}
    (Bool.elim {P = λ q → (((_＝_ ↑ true) ↑ q) ↑ c) x y}
      (inl $ inr $ inr refl)
      (Bool.elim {P = λ q → (((_＝_ ↑ true) ↑ false) ↑ q) x y}
         (inr $ inl $ inr refl)
         (inr $ inr $ inl refl)
         c)
      b)
    (Bool.elim {P = λ q → (((_＝_ ↑ false) ↑ q) ↑ c) x y}
       (Bool.elim {P = λ q → (((_＝_ ↑ false) ↑ true) ↑ q) x y}
         (inr $ inr $ inl refl)
         (inr $ inl $ inr refl)
         c)
       (inl $ inr $ inr refl)
       b)
    a

-- TODO arbitrary fintypes
-- af-fin : ∀ {n} → AF {A = Fin n} _＝_
-- af-fin = {!!}

af-≤ : AF _≤_
af-≤ = af-mono ≯→≤ (WFdec→AF <-is-wf λ x y → <-dec)

-- relation combinators
-- TODO could also be made into data?

-- restriction

_⇓_ : {A : 𝒰 ℓ}
    → (A → A → 𝒰 ℓ′) → (P : A → 𝒰 ℓ″)
    → Σ[ a ꞉ A ] P a → Σ[ a ꞉ A ] P a → 𝒰 ℓ′
(R ⇓ P) x y = R (fst x) (fst y)

-- computational Star with explicit length index
pow : {A : 𝒰 ℓ}
    → ℕ → (A → A → 𝒰 ℓ′) → A → A → 𝒰 (ℓ ⊔ ℓ′)
pow {ℓ′}      zero   R x y = Lift ℓ′ (x ＝ y)
pow      {A} (suc n) R x y = Σ[ z ꞉ A ] R x z × pow n R z y

-- sum lifts

_↑⊎_ : (A → A → 𝒰 ℓ′) → (B → B → 𝒰 ℓ′)
     → A ⊎ B → A ⊎ B → 𝒰 ℓ′
_↑⊎_ R _ (inl ax) (inl ay) = R ax ay
_↑⊎_ _ _ (inl _)  (inr _)  = ⊥
_↑⊎_ _ _ (inr _)  (inl _)  = ⊥
_↑⊎_ _ T (inr bx) (inr by) = T bx by

_↑⊎-l : (A → A → 𝒰 ℓ′)
      → A ⊎ B → A ⊎ B → 𝒰 ℓ′
_↑⊎-l R (inl ax) (inl ay) = R ax ay
_↑⊎-l _ (inl _)  (inr _)  = ⊥
_↑⊎-l _ (inr _)  (inl _)  = ⊥
_↑⊎-l _ (inr _)  (inr _)  = ⊤

_↑⊎-r : (B → B → 𝒰 ℓ′)
      → A ⊎ B → A ⊎ B → 𝒰 ℓ′
_↑⊎-r _ (inl _)  (inl _)  = ⊤
_↑⊎-r _ (inl _)  (inr _)  = ⊥
_↑⊎-r _ (inr _)  (inl _)  = ⊥
_↑⊎-r T (inr bx) (inr by) = T bx by

-- maybe

_↑ᵐ : (A → A → 𝒰 ℓ′)
    → Maybe A → Maybe A → 𝒰 ℓ′
_↑ᵐ R (just x) (just y) = R x y
_↑ᵐ _ (just _)  nothing = ⊥
_↑ᵐ _  nothing (just _) = ⊥
_↑ᵐ _  nothing  nothing = ⊤

---- AF combinators

-- products

af-×-fst : {A B : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
         → AF R → AF {A = A × B} (λ x y → R (x .fst) (y .fst))
af-×-fst = af-comap fst

af-×-snd : {A B : 𝒰 ℓ} {T : B → B → 𝒰 ℓ′}
         → AF T → AF {A = A × B} (λ x y → T (x .snd) (y .snd))
af-×-snd = af-comap snd

af-× : {A B : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′} {T : B → B → 𝒰 ℓ′}
     → AF R → AF T
     → AF (λ x y → R (x .fst) (y .fst) × T (x .snd) (y .snd))
af-× ar at = af-inter (af-×-fst ar) (af-×-snd at)

-- sums

af-⊎-l : AF R → AF (λ x y → R x y ⊎ T x y)
af-⊎-l = af-mono inl

af-⊎-r : AF T → AF (λ x y → R x y ⊎ T x y)
af-⊎-r = af-mono inr

af-↑⊎-l : ∀ {ℓa ℓb ℓr} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓr}
        → AF R → AF {A = A ⊎ B} (R ↑⊎-l)
af-↑⊎-l    (AFfull f) =
  AFlift λ where
             (inl a₁) → AFlift λ where
                                   (inl a₂) → AFfull λ _ _ → inr $ inr $ f a₁ a₂
                                   (inr b₂) → AFfull λ where
                                                         (inl x) (inl y) → inl $ inl $ f x y
                                                         (inl x) (inr _) → inl $ inr $ f a₁ x
                                                         (inr _)  _      → inr $ inl $ lift tt
             (inr b₁) → AFlift λ where
                                   (inl a₂) → AFfull λ where
                                                         (inl x) (inl y) → inl $ inl $ f x y
                                                         (inl x) (inr _) → inr $ inl $ f a₂ x
                                                         (inr _)  _      → inl $ inr $ lift tt
                                   (inr b₂) → AFfull λ _ _ → inr $ inr $ lift tt
af-↑⊎-l {B} (AFlift l) = AFlift λ where
                                (inl a) → af-mono
                                            (λ where
                                                 {x = inl _} {y = inl _} p → p
                                                 {x = inl _} {y = inr _} p → absurd (lower p)
                                                 {x = inr _} {y = inl _} p → absurd (lower p)
                                                 {x = inr _} {y = inr _} _ → inl $ lift tt)
                                            (af-↑⊎-l (l a))
                                (inr b) → AFlift λ where
                                                     (inl a′) → af-mono
                                                                   (λ where
                                                                        {x = inl _} {y = inl _} (inl rxy) → inl $ inl rxy
                                                                        {x = inl _} {y = inl _} (inr rax) → inr $ inl rax
                                                                        {x = inl _} {y = inr _} p         → absurd (lower p)
                                                                        {x = inr _} {y = inl _} p         → absurd (lower p)
                                                                        {x = inr _} {y = inr _} _         → inl $ inl $ lift tt)
                                                                   (af-↑⊎-l (l a′))
                                                     (inr b′) → AFfull λ x y → inr $ inr $ lift tt

af-↑⊎-r : ∀ {ℓa ℓb ℓt} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {T : B → B → 𝒰 ℓt}
        → AF T → AF {A = A ⊎ B} (T ↑⊎-r)
af-↑⊎-r {T} =
    af-rel-morph
      (λ u v → [ (λ y → v ＝ inr y) , (λ x → v ＝ inl x) ]ᵤ u)
      (λ where
           (inl ay) → inr ay , refl
           (inr by) → inl by , refl)
      (λ where
           (inl ax₁) (inl ax₂) (inl ay₁) (inl ay₂) h₁ h₂ lt → lift tt
           (inl ax₁) (inl ax₂) (inl ay₁) (inr by₂) h₁ h₂ lt → false! h₁
           (inl ax₁) (inl ax₂) (inr by₁) (inl ay₂) h₁ h₂ lt → false! h₂
           (inl ax₁) (inl ax₂) (inr by₁) (inr by₂) h₁ h₂ lt → subst (λ q → T q   by₂) (inr-inj h₁ ⁻¹) $
                                                              subst (      T ax₁    ) (inr-inj h₂ ⁻¹) lt
           (inl ax₁) (inr bx₂)  y₁        y₂       h₁ h₂ lt → absurd (lower lt)
           (inr bx₁) (inl ax₂)  y₁        y₂       h₁ h₂ lt → absurd (lower lt)
           (inr bx₁) (inr bx₂) (inl ay₁) (inl ay₂) h₁ h₂ lt → lift tt
           (inr bx₁) (inr bx₂) (inl ay₁) (inr by₂) h₁ h₂ lt → false! h₂
           (inr bx₁) (inr bx₂) (inr by₁)  y₂       h₁ h₂ lt → false! h₁)
  ∘ af-↑⊎-l

af-↑⊎ : ∀ {ℓa ℓb} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {R : A → A → 𝒰 ℓ′} {T : B → B → 𝒰 ℓ′}
      → AF R → AF T → AF (R ↑⊎ T)
af-↑⊎ ar at =
  af-mono
    (λ where
         {x = inl x} {y = inl y} (rxy , _) → rxy
         {x = inl x} {y = inr y} (b , _)   → absurd (lower b)
         {x = inr x} {y = inl y} (b , _)   → absurd (lower b)
         {x = inr x} {y = inr y} (_ , txy) → txy)
    (af-inter (af-↑⊎-l ar) (af-↑⊎-r at))

af-maybe : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
         → AF R → AF (R ↑ᵐ)
af-maybe {R} =
  af-rel-morph
             (λ where
                  (inl x) (just y) → x ＝ y
                  (inl x) nothing  → ⊥
                  (inr x) (just y) → ⊥
                  (inr x) nothing  → ⊤)
             (λ where
                  (just x) → inl x         , refl
                  nothing  → inr tt , lift tt)
             (λ where
                  (inl x₁) x₂       nothing   y₂        h₁ h₂ lt → absurd (lower h₁)
                  (inl x₁) (inl x₂) (just y₁) (just y₂) h₁ h₂ lt → subst (λ q → R q  y₂) h₁ $
                                                                   subst (      R x₁   ) h₂ lt
                  (inl x₁) (inl x₂) (just y₁) nothing   h₁ h₂ lt → absurd (lower h₂)
                  (inl x₁) (inr tt) (just y₁) y₂        h₁ h₂ lt → absurd (lower lt)
                  (inr x₁) x₂       (just y₁) y₂        h₁ h₂ lt → absurd (lower h₁)
                  (inr x₁) (inl x₂) nothing   y₂        h₁ h₂ lt → absurd (lower lt)
                  (inr x₁) (inr x₂) nothing   (just y₂) h₁ h₂ lt → absurd (lower h₂)
                  (inr x₁) (inr x₂) nothing   nothing   h₁ h₂ lt → lift tt)
  ∘ af-↑⊎-l

-- restrictions

af-⇓ : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′} {P : A → 𝒰 ℓ″}
     → AF R → AF (R ⇓ P)
af-⇓ {R} = af-comap fst

af-↑→⇓ : ∀ {a}
       → AF (R ↑ a) → AF (R ⇓ (λ x → ¬ R a x))
af-↑→⇓ {R} {a} =
  af-rel-morph (λ x y → x ＝ fst y) (λ y → fst y , refl)
    λ x₁ x₂ y₁ y₂ e₁ e₂ → [ subst (λ q → R q (fst y₂)) e₁ ∘ subst (R x₁) e₂
                          , (λ rax₁ → absurd (snd y₁ (subst (R a) e₁ rax₁)))
                          ]ᵤ

af-dec⇓→↑ : {A B : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
          → ∀ {a}
          → (∀ x → Dec (R a x))
          → AF (R ⇓ (λ x → ¬ R a x))
          → AF (R ↑ a)
af-dec⇓→↑ {A} {R} {a} dr ar =
  af-rel-morph
    (λ where
         (inl x) y → fst x ＝ y
         (inr x) y → fst x ＝ y)
    (λ y → Dec.rec (λ ray  → inl (y , ray)  , refl)
                   (λ nray → inr (y , nray) , refl)
                   (dr y))
    (λ where
         (inl x₁) (inl x₂) y₁ y₂ e₁ e₂ r → inr $ subst (R a) e₁ (snd x₁)
         (inl x₁) (inr x₂) y₁ y₂ e₁ e₂ r → absurd (lower r)
         (inr x₁) (inl x₂) y₁ y₂ e₁ e₂ r → absurd (lower r)
         (inr x₁) (inr x₂) y₁ y₂ e₁ e₂ r → inl $ subst (λ q → R q        y₂) e₁ $
                                                 subst (      R (fst x₁)   ) e₂ r)
    (af-↑⊎ {A = Σ[ x ꞉ A ] R a x} af-unit ar)
