{-# OPTIONS --safe #-}
module Data.Vec.Membership where

open import Foundations.Base

open import Correspondences.Base
open import Correspondences.Unary.Decidable

open import Data.Empty.Base
open import Data.Fin.Base
import Data.Dec.Base as Dec
open import Data.Vec.Properties

open import Meta.Discrete

open import Data.Vec.Correspondences.Unary.Any
open import Data.Vec.Correspondences.Unary.All

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  P : A → Type ℓ′
  x : A
  n : ℕ
  @0 xs : Vec A n

_∈_ : A → Vec A n → Type _
x ∈ xs = Σ[ idx ꞉ Fin _ ] (lookup xs idx ＝ x)

_∉_ : A → Vec A n → Type _
x ∉ xs = ¬ (x ∈ xs)

_∈!_ : A → Vec A n → Type _
x ∈! xs = is-contr (x ∈ xs)

_∈?_ : ⦃ Discrete A ⦄ → Π[ x ꞉ A ] Π[ as ꞉ Vec A n ] Dec (x ∈ as)
_∈?_ {n = 0} x []       = no λ ()
_∈?_ {n = _} x (a ∷ as) with a ≟ x
... | yes p = yes (fzero , p)
... | no ¬p with x ∈? as
... | yes (i , q) = yes (fsuc i , q)
... | no ¬q = no λ { (fzero , p) → ¬p p ; (fsuc i , q) → ¬q (i , q) }

any→exists : {n : ℕ} {xs : Vec A n} → Any P xs → Σ[ a ꞉ A ] Σ[ pa ꞉ P a ] (a ∈ xs)
any→exists {n = suc _} {xs = _ ∷ _} (here  p)  = _ , p , fzero , refl
any→exists {n = suc _} {xs = _ ∷ _} (there ps) = let a , pa , i , q = any→exists ps in a , pa , fsuc i , q

-- exists→any : (z : Σ[ a ꞉ A ] P a) → (z .fst ∈ xs) → Any P xs
-- exists→any (a , pa) (here  r)  = here $ subst _ (sym r) pa
-- exists→any (a , pa) (there rs) = there (exists→any (a , pa) rs)

-- ∀¬-absurd : All (¬_ ∘ P) xs → x ∈ xs → P x → ⊥
-- ∀¬-absurd (p ∷ ps) (here  r)  px = p (subst _ (sym r) px)
-- ∀¬-absurd (p ∷ ps) (there rs) px = ∀¬-absurd ps rs px
