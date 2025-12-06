{-# OPTIONS --safe #-}
module Data.Star.Path where

open import Foundations.Base
open import Foundations.HLevel
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Star.Base

private variable
  ℓ ℓ′ : Level
  A B : 𝒰 ℓ
  g : A → A → 𝒰 ℓ′
  x x′ y y′ z : A

-- TODO arbitrary levels+2

StarLen : (A → A → 𝒰 ℓ′)
        → ℕ → A → A → 𝒰 (level-of-type A ⊔ ℓ′)
StarLen {ℓ′} g  zero   s t = Lift ℓ′ (s ＝ t)
StarLen {A}  g (suc n) s t = Σ[ x ꞉ A ] g s x × StarLen g n x t

is-set-StarLen : is-set A
               → (∀ x y → is-set (g x y))
               → ∀ n (s t : A)
               → is-set (StarLen g n s t)
is-set-StarLen sv  se zero   s t =
  Lift-is-of-hlevel 2 $
  is-prop→is-set $
  path-is-of-hlevel 1 sv s t
is-set-StarLen sv se (suc n) s t =
  Σ-is-of-hlevel 2 sv λ x →
    ×-is-of-hlevel 2
      (se s x)
      (is-set-StarLen sv se n x t)

ΣStarLen : (A → A → 𝒰 ℓ′)
         → A → A → 𝒰 (level-of-type A ⊔ ℓ′)
ΣStarLen g s t = Σ[ n ꞉ ℕ ] StarLen g n s t

is-set-ΣStarLen : is-set A
                → (∀ x y → is-set (g x y))
                → (s t : A)
                → is-set (ΣStarLen g s t)
is-set-ΣStarLen sa se s t =
  Σ-is-of-hlevel 2 (hlevel 2) λ n → is-set-StarLen sa se n s t

Star→ΣStarLen : ∀ {x y} → Star g x y → ΣStarLen g x y
Star→ΣStarLen (ε e)      = 0 , lift e
Star→ΣStarLen (xw ◅ rwy) =
  let (n , sl) = Star→ΣStarLen rwy in
  suc n , _ , (xw , sl)

ΣStarLen→Star : ∀ {x y} → ΣStarLen g x y → Star g x y
ΣStarLen→Star (zero           , rl) = ε (rl .lower)
ΣStarLen→Star (suc n , w , xw , rl) = xw ◅ ΣStarLen→Star (n , rl)

Star→ΣStarLen→Star : ∀ {x y} (r : Star g x y) → ΣStarLen→Star (Star→ΣStarLen r) ＝ r
Star→ΣStarLen→Star (ε r)      = refl
Star→ΣStarLen→Star (xw ◅ rwy) = ap² _◅_ refl (Star→ΣStarLen→Star rwy)

is-set-Star : is-set A
            → (∀ x y → is-set (g x y))
            → {s t : A} → is-set (Star g s t)
is-set-Star sv se {s} {t} =
  retract→is-of-hlevel 2
    (ΣStarLen→Star , make-section Star→ΣStarLen (fun-ext Star→ΣStarLen→Star))
    (is-set-ΣStarLen sv se s t)
