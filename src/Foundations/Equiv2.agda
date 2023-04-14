{-# OPTIONS --safe #-}
module Foundations.Equiv2 where

open import Foundations.Prelude
open import Foundations.HLevel

private variable ℓ ℓ′ ℓ″ ℓ‴ : Level

-- I said real symmetry
infix 4 _≃_
record _≃_ {ℓ} (A : Type ℓ) (B : Type ℓ) : Type (ℓsuc ℓ) where
  eta-equality
  field
    R : A → B → Type ℓ
    forward  : Π[ x ꞉ A ] is-contr  (Σ[ y ꞉ B ]   id R x y)
    backward : Π[ y ꞉ B ] is-contr⁻ (Σ[ x ꞉ A ] flip R y x)
open _≃_ public

private variable
  A B C : Type ℓ

to : (A ≃ B) → A → B
to e x = e .forward x .fst .fst

from : (A ≃ B) → B → A
from e y = e .backward y .fst .fst

inv-eq : A ≃ B → B ≃ A
inv-eq e .R          = flip (e .R)
inv-eq e .forward  y = let x , p = e .backward y in x , λ _ → sym (p _)
inv-eq e .backward x = let y , p = e .forward  x in y , λ _ → sym (p _)

-- definitionally involutive
inv-eq-invol : {e : A ≃ B} → inv-eq (inv-eq e) ＝ e
inv-eq-invol = refl

idₑ : A ≃ A
idₑ .R x y = x ＝ y
idₑ .forward  x = Singleton-is-contr   (x , refl)
idₑ .backward x = Singleton⁻-is-contr⁻ (x , refl)

open import Prim.Data.Nat
data Fin : @0 ℕ → Type where
  ze : ∀ {n} → Fin (suc n)
  su : ∀ {n} → Fin n → Fin (suc n)

-- data Sum (A B : Type ℓ) {n : ℕ} : (k : Fin n) → Type ℓ where
--   one : A → Sum A B ze
--   two : B → Sum A B (su ?)

-- infixr 29 _∙ₑ_
-- _∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
-- (f ∙ₑ g) .R x z = Σ[ len ꞉ ℕ ] ((k : Fin len) → Sum (f .R x (to f x)) (g .R (from g z) z) k)
-- -- (f ∙ₑ g) .R x z = f .R x (to f x) × g .R (from g z) z

-- (f ∙ₑ g) .forward x = ((to g ∘ to f $ x) , 2 , test) , {!!}
--   where
--   test : Fin 2 → Sum _ _ 2
--   test ze = {!!}
--   test (su x) = {!!}

-- (f ∙ₑ g) .backward z = ((from f ∘ from g $ z) , 2 , {!!}) , {!!}

-- -- kekw : (e : B ≃ C) (y : B) (z : C) → (y ＝ y) × e .R (e .backward z) z
-- -- kekw e y z = refl , let tt = inhabited-prop-is-contr {!!} {!!} in tt .fst

-- unital-left : (e : B ≃ C) → idₑ ∙ₑ e ＝ e
-- unital-left e i .R y z = {!!}
-- unital-left e i .forward = {!!}
-- unital-left e i .backward = {!!}
