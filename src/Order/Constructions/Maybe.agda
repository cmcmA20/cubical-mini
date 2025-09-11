{-# OPTIONS --safe #-}
module Order.Constructions.Maybe where

open import Prelude

open import Order.Base
open import Order.Strict
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet

open import Data.Empty hiding (_≠_)
open import Data.Reflects
open import Data.Sum
open import Data.Maybe
open import Data.Acc
open import Data.AF

private variable
  o ℓ : Level
  A : 𝒰 o

-- adjoin a bottom : nothing < just

-- TODO rename to ↑ᵐ or some version thereof
Maybe≤ : (A → A → 𝒰 ℓ)
       → Maybe A → Maybe A → 𝒰 ℓ
Maybe≤ {ℓ} le  nothing  y       = ⊤
Maybe≤     le (just x) (just y) = le x y
Maybe≤     le (just x)  nothing = ⊥

Maybe≤-thin : {A : 𝒰 o} {le : A → A → 𝒰 ℓ} {mx my : Maybe A}
            → (∀ {x y} → is-prop (le x y))
            → is-prop (Maybe≤ le mx my)
Maybe≤-thin {mx = nothing}               lp = hlevel 1
Maybe≤-thin {mx = just x} {my = just y}  lp = lp
Maybe≤-thin {mx = just x} {my = nothing} lp = hlevel 1

Maybe≤-just-l : {A : 𝒰 o} {le : A → A → 𝒰 ℓ} {x : A} {my : Maybe A}
              → Maybe≤ le (just x) my
              → Σ[ y ꞉ A ] (my ＝ just y) × le x y
Maybe≤-just-l {my = just y} mle = y , refl , mle

Maybeₚ : Poset o ℓ → Poset o ℓ
Maybeₚ {ℓ} P = po module Maybeₚ where
  module P = Poset P

  po : Poset _ _
  po .Poset.Ob = Maybe ⌞ P ⌟
  po .Poset._≤_ = Maybe≤ P._≤_
  po .Poset.≤-thin {x} {y} = Maybe≤-thin {mx = x} {my = y} (hlevel 1)
  po .Poset.≤-refl {x = nothing} = lift tt
  po .Poset.≤-refl {x = just x}  = refl
  po .Poset.≤-trans {x = nothing}                          _  _  = lift tt
  po .Poset.≤-trans {x = just x} {y = just y} {z = just z} xy yz = xy ∙ yz
  po .Poset.≤-antisym {x = nothing} {y = nothing} _ _ = refl
  po .Poset.≤-antisym {x = just x} {y = just y} xy yx = ap just (P.≤-antisym xy yx)

instance
  Maybe-bottom : {P : Poset o ℓ} → Bottom (Maybeₚ P)
  Maybe-bottom .Bottom.bot = nothing
  Maybe-bottom .Bottom.bot-is-bot x = lift tt

module _ {P : Poset o ℓ} where
  Just : P ⇒ Maybeₚ P
  Just .hom = just
  Just .pres-≤ = id

Maybe-af : {le : A → A → 𝒰 ℓ}
         → AF le → AF (Maybe≤ le)
Maybe-af {le} =
    af-rel-morph
      (λ where
           (inl x) (just y) → x ＝ y
           (inl x)  nothing → ⊥
           (inr x) (just y) → ⊥
           (inr x)  nothing → ⊤)
      (λ where
           (just x) → inl x  , refl
           nothing  → inr tt , lift tt)
      (λ where
           (inl x₁) (inl x₂) (just y₁) (just y₂) h₁ h₂ l → subst (λ q → le q  y₂) h₁ $
                                                           subst (      le x₁   ) h₂ l
           (inl x₁) (inl x₂) (just y₁)  nothing  h₁ h₂ l → false! h₂
           (inl x₁) (inl x₂)  nothing   y₂       h₁ h₂ l → lift tt
           (inr x₁) (inl x₂) (just y₁) (just y₂) h₁ h₂ l → false! h₁
           (inr x₁) (inr x₂) (just y₁) (just y₂) h₁ h₂ l → false! h₁
           (inr x₁) (inr x₂) (just y₁)  nothing  h₁ h₂ l → false! h₁
           (inr x₁) (inr x₂)  nothing  (just y₂) h₁ h₂ l → false! h₂
           (inr x₁) (inr x₂)  nothing   nothing  h₁ h₂ l → lift tt)
  ∘ af-↑⊎-l

-- strict

Maybe< : (A → A → 𝒰 ℓ)
       → Maybe A → Maybe A → 𝒰 ℓ
Maybe< lt  nothing (just y) = ⊤
Maybe< lt  nothing  nothing = ⊥
Maybe< lt (just x) (just y) = lt x y
Maybe< lt (just x)  nothing = ⊥

¬<nothing : {lt : A → A → 𝒰 ℓ}
            {x : Maybe A}
          → ¬ (Maybe< lt x nothing)
¬<nothing {x = just x}  = lower
¬<nothing {x = nothing} = lower

Maybe<-lr : {A : 𝒰 o} {lt : A → A → 𝒰 ℓ} {mx my : Maybe A}
          → Maybe< lt mx my
          → Σ[ y ꞉ A ] (my ＝ just y) × ((x : A) → mx ＝ just x → lt x y)
Maybe<-lr {lt} {mx = just x}  {my = just y} mlt =
  y , refl , λ x e → subst (λ q → lt q y) (just-inj e) mlt
Maybe<-lr      {mx = nothing} {my = just y} mlt =
  y , refl , λ x → false!

Maybe<-irr : {lt : A → A → 𝒰 ℓ}
           → (∀ {x} → ¬ lt x x)
           → {x : Maybe A}
           → ¬ (Maybe< lt x x)
Maybe<-irr li {x = just x}  = li
Maybe<-irr li {x = nothing} = lower

Maybeₛ : StrictPoset o ℓ → StrictPoset o ℓ
Maybeₛ {ℓ} S = spo module Maybeₛ where
  module S = StrictPoset S

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = Maybe ⌞ S ⌟
  spo .StrictPoset._<_ = Maybe< S._<_
  spo .StrictPoset.<-thin {x = just x}  {y = just y}  = hlevel 1
  spo .StrictPoset.<-thin {x = just x}  {y = nothing} = hlevel 1
  spo .StrictPoset.<-thin {x = nothing} {y = just y}  = hlevel 1
  spo .StrictPoset.<-thin {x = nothing} {y = nothing} = hlevel 1
  spo .StrictPoset.<-irrefl {x} = Maybe<-irr S.<-irrefl {x = x}
  spo .StrictPoset.<-trans {x = just x}  {y = just y} {z = just z} xy yz = xy ∙ yz
  spo .StrictPoset.<-trans {x = nothing} {y = just y} {z = just z} xy yz = lift tt

-- well-foundedness

Maybe-acc : {lt : A → A → 𝒰 ℓ}
            {x : A}
          → Acc lt x
          → Acc (Maybe< lt) (just x)
Maybe-acc (acc rec) = acc λ where
                              (just y) y< → Maybe-acc (rec y y<)
                              nothing y< → acc λ y y< → absurd (¬<nothing {x = y} y<)

Maybe-wf : {lt : A → A → 𝒰 ℓ}
         → is-wf lt
         → is-wf (Maybe< lt)
Maybe-wf wf (just x) = Maybe-acc (wf x)
Maybe-wf wf nothing = acc λ y y< → absurd (¬<nothing {x = y} y<)

-- interaction

Maybe≤→¬> : {ma mb : Maybe A}
            {le lt : A → A → 𝒰 ℓ}
          → (∀ {x y} → le x y → lt y x → ⊥)
          → Maybe≤ le ma mb → Maybe< lt mb ma → ⊥
Maybe≤→¬> {ma = just a}  {mb = just b}  lenlt mle mlt = lenlt mle mlt
Maybe≤→¬> {ma = nothing} {mb = nothing} lenlt mle mlt = lower mlt

Maybe<→¬≥ : {ma mb : Maybe A}
            {le lt : A → A → 𝒰 ℓ}
          → (∀ {x y} → lt x y → le y x → ⊥)
          → Maybe< lt ma mb → Maybe≤ le mb ma → ⊥
Maybe<→¬≥ {ma = just a}  {mb = just b}  ltnle mlt mle = ltnle mlt mle
Maybe<→¬≥ {ma = nothing} {mb = nothing} ltnle mlt mle = lower mlt

Maybe¬>→≤ : {ma mb : Maybe A}
            {le lt : A → A → 𝒰 ℓ}
          → (∀ {x y} → ¬ lt y x → le x y)
          → ¬ Maybe< lt mb ma → Maybe≤ le ma mb
Maybe¬>→≤ {ma = just a}  {mb = just b}  nltle nmlt = nltle nmlt
Maybe¬>→≤ {ma = just a}  {mb = nothing} nltle nmlt = lift (nmlt (lift tt))
Maybe¬>→≤ {ma = nothing} {mb = just b}  nltle nmlt = lift tt
Maybe¬>→≤ {ma = nothing} {mb = nothing} nltle nmlt = lift tt

Maybe¬≥→< : {ma mb : Maybe A}
            {le lt : A → A → 𝒰 ℓ}
          → (∀ {x y} → ¬ le y x → lt x y)
          → ¬ Maybe≤ le mb ma → Maybe< lt ma mb
Maybe¬≥→< {ma = just a}  {mb = just b}  nlelt nmle = nlelt nmle
Maybe¬≥→< {ma = just a}  {mb = nothing} nlelt nmle = lift (nmle (lift tt))
Maybe¬≥→< {ma = nothing} {mb = just b}  nlelt nmle = lift tt
Maybe¬≥→< {ma = nothing} {mb = nothing} nlelt nmle = lift (nmle (lift tt))
