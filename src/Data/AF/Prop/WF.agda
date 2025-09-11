{-# OPTIONS --safe #-}
module Data.AF.Prop.WF where

open import Meta.Prelude
open import Meta.Effect
open Variadics _

open import Data.AF.Prop
open import Data.Acc.Base
open import Data.Acc.Path
open import Data.Acc.Properties
open import Data.Empty.Base
open import Data.Dec.Base as Dec
open import Data.Sum.Base as ⊎
open import Data.Star.Base
open import Data.Plus.Base
open import Data.Plus.Properties
open import Data.Truncation.Propositional as ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

AF₁→Acc : AF₁ R
        → ∀ {y} → (∀ {x z} → Plus T x z → R z x → Star T z y → ⊥)
        → Acc T y
AF₁→Acc (AF₁full f)       {y} cm =
  acc λ w Tw → absurd (rec! (λ ryw → cm [ Tw ]⁺ ryw (ε refl)) (f y w))
AF₁→Acc (AF₁lift l)       {y} cm =
  acc λ w Tw →
    AF₁→Acc (l y) λ Pxz rr Szw →
      rec! [ (λ Rzx → cm Pxz Rzx (Szw ◅+ Tw) )
           , (λ Ryx → cm (Szw ◅⋆∷ Tw) Ryx (ε refl))
           ]ᵤ rr
AF₁→Acc (AF₁squash a b i) {y} cm =
  acc-is-prop y (AF₁→Acc a cm) (AF₁→Acc b cm) i

WFdec→AF : is-wf R
         → (∀ x y → Dec (R x y))
         → AF₁ (λ x y → ¬ (R y x))
WFdec→AF {R} wf dec =
  AF₁lift $
  to-induction wf
    (λ q → AF₁ ((λ x y → ¬ₜ R y x) ↑₁ q))
    λ b ih → AF₁lift λ a →
      Dec.rec
         (λ rab  → af₁-mono (map (⊎.dmap (∣_∣₁ ∘ inl) (∣_∣₁ ∘ inl))) (ih a rab))
         (λ nrab → AF₁full λ x y → ∣ ∣ inr ∣ inr nrab ∣₁ ∣₁ ∣₁)
         (dec a b)

AF₁→WF : AF₁ R
      → (∀ {x y} → Plus T x y → R y x → ⊥)
      → is-wf T
AF₁→WF af cm y = AF₁→Acc af λ Pxz Rzx _ → cm Pxz Rzx

WQO₁→WF : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
        → AF₁ R → Trans R
        → is-wf (λ x y → R x y × (¬ R y x))
WQO₁→WF {A} {R} af tr = AF₁→WF af go
  where
  go : {x y : A} →
       Plus (λ a b → R a b × (¬ R b a)) x y → R y x → ⊥
  go [ _ , nryx ]⁺ ryx = nryx ryx
  go ((rxw , nrwx) ◅⁺ p) ryx = go p (tr ._∙_ ryx rxw)

WQO₁-antisym→WF : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
                → AF₁ R → Trans R → (∀ x y → R x y → R y x → x ＝ y)
                → is-wf (λ x y → R x y × (x ≠ y))
WQO₁-antisym→WF af tr as =
  wf-map
    (λ x y → λ where (rxy , ne) → rxy , contra (as x y rxy) ne)
    (WQO₁→WF af tr)

-- Noetherianness

AF₁→Noeth : AF₁ R
          → (∀ {x y} → Plus (flip T) x y → R y x → ⊥)
          → is-noeth T
AF₁→Noeth = AF₁→WF

WQO₁→Noeth : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
          → AF₁ R → Trans R
          → is-noeth (λ x y → R y x × (¬ R x y))
WQO₁→Noeth = WQO₁→WF

WQO₁-antisym→Noeth : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
                  → AF₁ R → Trans R → (∀ x y → R x y → R y x → x ＝ y)
                  → is-noeth (λ x y → R y x × (y ≠ x))
WQO₁-antisym→Noeth = WQO₁-antisym→WF

