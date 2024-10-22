{-# OPTIONS --safe #-}
module Order.Height where

open import Cat.Prelude
open import Order.Constructions.Nat
open import Order.Diagram.Bottom
open import Order.Diagram.Lub
open import Order.Strict

open import Data.Acc
open import Data.Nat.Base
open import Data.Nat.Order.Base
  hiding (_<_; _≤_; _≮_)
open import Data.Nat.Properties
open import Data.Reflects.Base
open import Data.Star

record is-of-height {o ℓ} (S : StrictPoset o ℓ) (n : ℕ) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
  open StrictPoset S
  field
    has-height : is-lub ℕₚ {I = Substar _<_} (suc ∘ₜ star-len ∘ₜ Substar.path) n

private variable n : ℕ

module _ {o ℓ} {S : StrictPoset o ℓ} where
  open StrictPoset S
  open is-of-height
  open Bottom ℕ-bottom

  height0→empty : is-of-height S 0 → ¬ ⌞ S ⌟
  height0→empty h0 x = false! $ h0 .has-height .is-lub.fam≤lub $ sst x x refl

  empty→height0 : ¬ ⌞ S ⌟ → is-of-height S 0
  empty→height0 ¬s .has-height .is-lub.fam≤lub (sst x _ _) = ⊥.rec (¬s x)
  empty→height0 ¬s .has-height .is-lub.least _ _ = ¡

  height1→discrete : is-of-height S 1 → Π[ _≮_ ]
  height1→discrete h1 x y x<y = false! $ h1 .has-height .is-lub.fam≤lub (sst x y (x<y ◅ refl))

  inhabited-discrete→height1 : ∥ ⌞ S ⌟ ∥₁ → Π[ _≮_ ] → is-of-height S 1
  inhabited-discrete→height1 _ d .has-height .is-lub.fam≤lub (sst _ _ (ε _)) = refl
  inhabited-discrete→height1 _ d .has-height .is-lub.fam≤lub (sst x _ (xw ◅ _)) = false! $ d x _ xw
  inhabited-discrete→height1 p _ .has-height .is-lub.least ub f = rec! (λ p′ → f (sst p′ p′ refl)) p

  height-wf-ind : is-of-height S n
                → ∀ {ℓ″} (P : ⌞ S ⌟ → 𝒰 ℓ″)
                → ((x : ⌞ S ⌟) → Π[ (_< x) ⇒ P ] → P x)
                → Π[ P ]
  height-wf-ind {n} h P ih x = go x refl n refl
    where
    go : (a : ⌞ S ⌟) (s : Star _<_ a x) (m : ℕ) → m ＝ n ∸ star-len s → P a
    go a s  zero   e = ⊥.rec $
      (<≃≱ $ <≃suc≤ $ h .has-height .is-lub.fam≤lub (sst a x s)) (∸=0→≤ (e ⁻¹))
    go a s (suc m) e =
      ih a λ y y<x →
        go y (y<x ◅ s) m
          ( ap pred e
          ∙ pred=∸1 (n ∸ star-len s)
          ∙ ∸-+-assoc (star-len s) n 1 ⁻¹
          ∙ ap (n ∸_) (+-comm (star-len s) 1))

  height→wf : ∀ {n} → is-of-height S n → is-wf _<_
  height→wf h = from-induction (height-wf-ind h)

  height-noeth-ind : is-of-height S n
                   → ∀ {ℓ″} (P : ⌞ S ⌟ → 𝒰 ℓ″)
                   → ((x : ⌞ S ⌟) → Π[ (x <_) ⇒ P ] → P x)
                   → Π[ P ]
  height-noeth-ind {n} h P ih x = go x refl n refl
    where
    go : (a : ⌞ S ⌟) (s : Star _<_ x a) (m : ℕ) → m ＝ n ∸ star-len s → P a
    go a s  zero   e = ⊥.rec $
        (<≃≱ $ <≃suc≤ $ h .has-height .is-lub.fam≤lub (sst x a s)) (∸=0→≤ (e ⁻¹))
    go a s (suc m) e =
      ih a λ y a<y →
         go y (s ◅+ a<y) m
           (ap pred e
          ∙ pred=∸1 (n ∸ star-len s)
          ∙ ∸-+-assoc (star-len s) n 1 ⁻¹
          ∙ ap (n ∸_) (star-trans-len s (star-sng a<y)) ⁻¹)

  height→noeth : is-of-height S n → is-noeth _<_
  height→noeth h = from-ninduction (height-noeth-ind h)

  height→finite-height : is-of-height S n → is-of-finite-height _<_
  height→finite-height h = < height→wf h , height→noeth h >
