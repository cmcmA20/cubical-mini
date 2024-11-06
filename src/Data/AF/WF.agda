{-# OPTIONS --safe #-}
module Data.AF.WF where

open import Foundations.Base
open Variadics _

open import Data.AF.Base
open import Data.Acc.Base
open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Sum.Base
open import Data.Star.Base
open import Data.Plus.Base
open import Data.Plus.Properties

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

AF→Acc : AF R
       → ∀ {y} → (∀ {x z} → Plus T x z → R z x → Star T z y → ⊥)
       → Acc T y
AF→Acc (AFfull f) {y} cm = acc λ w Tw → absurd (cm [ Tw ]⁺ (f y w) (ε refl))
AF→Acc (AFlift l) {y} cm =
  acc λ w Tw →
  AF→Acc (l y) λ Pxz →
    λ where
        (inl Rzx) Szw → cm Pxz Rzx (Szw ◅+ Tw)
        (inr Ryx) Szw → cm (Szw ◅⋆∷ Tw) Ryx (ε refl)

-- well-foundedness

WFdec→AF : is-wf R
         → (∀ x y → Dec (R x y))
         → AF (λ x y → ¬ (R y x))
WFdec→AF {R} wf dec =
  AFlift $
  to-induction wf
    (λ q → AF ((λ x y → ¬ₜ R y x) ↑ q))
    λ b ih → AFlift λ a →
      Dec.rec
        (λ rab  → af-mono [ inl ∘ inl , inr ∘ inl ]ᵤ (ih a rab))
        (λ nrab → AFfull λ _ _ → inr (inr nrab))
        (dec a b)

AF→WF : AF R
      → (∀ {x y} → Plus T x y → R y x → ⊥)
      → is-wf T
AF→WF af cm y = AF→Acc af λ Pxz Rzx _ → cm Pxz Rzx

WQO→WF : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
       → AF R → Trans R
       → is-wf (λ x y → R x y × (¬ R y x))
WQO→WF {A} {R} af tr = AF→WF af go
  where
  go : {x y : A} →
       Plus (λ a b → R a b × (¬ R b a)) x y → R y x → ⊥
  go [ _ , nryx ]⁺ ryx = nryx ryx
  go ((rxw , nrwx) ◅⁺ p) ryx = go p (tr ._∙_ ryx rxw)

-- Noetherianness

AF→Noeth : AF R
         → (∀ {x y} → Plus (flip T) x y → R y x → ⊥)
         → is-noeth T
AF→Noeth af cm y = AF→Acc af λ Pxz Rzx _ → cm Pxz Rzx
