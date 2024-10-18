{-# OPTIONS --safe #-}
module Order.Height where

open import Cat.Prelude
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Order.Base
open import Data.Star.Base
open import Data.Reflects.Base
open import Data.Wellfounded.Base
open import Data.Wellfounded.Properties

open import Order.Strict
open import Order.Diagram.Lub
open import Order.Constructions.Nat

record is-of-height {o ℓ} (S : StrictPoset o ℓ) (n : ℕ) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
  field
    has-height : is-lub ℕₚ {I = Substar (S .StrictPoset._<_)} (suc ∘ₜ star-len ∘ₜ Substar.path) n

private variable
  o ℓ : Level
  S : StrictPoset o ℓ

height0→empty : is-of-height S 0 → ¬ ⌞ S ⌟
height0→empty h0 x =
  ⊥.rec (s≰z (h0 .is-of-height.has-height .is-lub.fam≤lub (sst x x (ε refl))))

empty→height0 : ¬ ⌞ S ⌟ → is-of-height S 0
empty→height0 ¬s .is-of-height.has-height .is-lub.fam≤lub (sst x _ _) = ⊥.rec (¬s x)
empty→height0 ¬s .is-of-height.has-height .is-lub.least ub f = z≤

height1→discrete : is-of-height S 1
                 → (∀ x y → ¬ (S .StrictPoset._<_ x y))
height1→discrete h1 x y x<y = ⊥.absurd (s≰z (≤-peel (h1 .is-of-height.has-height .is-lub.fam≤lub (sst x y (x<y ◅ ε refl)))))

inhabited-discrete→height1 : ∥ ⌞ S ⌟ ∥₁
                           → (∀ x y → ¬ (S .StrictPoset._<_ x y))
                           → is-of-height S 1
inhabited-discrete→height1 _ d .is-of-height.has-height .is-lub.fam≤lub (sst _ _ (ε _)) = ≤-refl
inhabited-discrete→height1 _ d .is-of-height.has-height .is-lub.fam≤lub (sst x _ (xw ◅ _)) = ⊥.rec (d x _ xw)
inhabited-discrete→height1 p _ .is-of-height.has-height .is-lub.least ub f = rec! (λ p′ → f (sst p′ p′ (ε refl))) p

height-wf-ind : ∀ {ℓ″} {n} → is-of-height S n
              → (P : ⌞ S ⌟ → 𝒰 ℓ″)
              → ((x : ⌞ S ⌟) → ((y : ⌞ S ⌟) → S .StrictPoset._<_ y x → P y) → P x)
              → (x : ⌞ S ⌟) → P x
height-wf-ind {S} {n} h P ih x =
  go x (ε refl) n refl
  where
  go : (a : ⌞ S ⌟) (s : Star (S .StrictPoset._<_) a x) (m : ℕ) → m ＝ n ∸ star-len s → P a
  go a s  zero   e =
    ⊥.rec
      ((<≃≱ $ <≃suc≤ $ h .is-of-height.has-height .is-lub.fam≤lub (sst a x s)) (∸=0→≤ (e ⁻¹)))
  go a s (suc m) e =
    ih a λ y y<x →
      go y (y<x ◅ s) m
        ( ap pred e
        ∙ pred=∸1 (n ∸ star-len s)
        ∙ ∸-+-assoc (star-len s) n 1 ⁻¹
        ∙ ap (n ∸_) (+-comm (star-len s) 1))

height→Wf : ∀ {n} → is-of-height S n → Wf (S .StrictPoset._<_)
height→Wf h = from-induction (height-wf-ind h)

height-noeth-ind : ∀ {ℓ″} {n} → is-of-height S n
              → (P : ⌞ S ⌟ → 𝒰 ℓ″)
              → ((x : ⌞ S ⌟) → ((y : ⌞ S ⌟) → S .StrictPoset._<_ x y → P y) → P x)
              → (x : ⌞ S ⌟) → P x
height-noeth-ind {S} {n} h P ih x =
  go x (ε refl) n refl
  where
  go : (a : ⌞ S ⌟) (s : Star (S .StrictPoset._<_) x a) (m : ℕ) → m ＝ n ∸ star-len s → P a
  go a s  zero   e =
    ⊥.rec
      ((<≃≱ $ <≃suc≤ $ h .is-of-height.has-height .is-lub.fam≤lub (sst x a s)) (∸=0→≤ (e ⁻¹)))
  go a s (suc m) e =
    ih a λ y a<y →
       go y (s ◅+ a<y) m
         (ap pred e
        ∙ pred=∸1 (n ∸ star-len s)
        ∙ ∸-+-assoc (star-len s) n 1 ⁻¹
        ∙ ap (n ∸_) (star-trans-len s (star-sng a<y)) ⁻¹)

height→Noeth : ∀ {n} → is-of-height S n → Noeth (S .StrictPoset._<_)
height→Noeth h = from-ninduction (height-noeth-ind h)

height→FinHeight : ∀ {n} → is-of-height S n → FinHeight (S .StrictPoset._<_)
height→FinHeight {n} h x = height→Wf h x , height→Noeth h x
