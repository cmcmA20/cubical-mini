{-# OPTIONS --safe #-}
module Foundations.Equiv' where

open import Prim.Equiv
open import Foundations.Prelude
open import Foundations.HLevel
open import Foundations.Path

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A A′ : Type ℓ
  B B′ : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to is-contr (fibre f b).
strict-contr-fibers : {f : A → B} (g : B → A) (b : B)
                    → Σ[ t  ꞉ fibre f (f (g b)) ]
                      Π[ t′ ꞉ fibre f       b   ]
                      Path (fibre f (f (g b))) t (g (f (t′ .fst)) , cong (f ∘ g) (t′ .snd))
strict-contr-fibers     g b .fst = g b , refl
strict-contr-fibers {f} g b .snd (a , p) i = g (p (~ i)) , λ j → f (g (p (~ i ∨ j)))

-- The identity equivalence
id-is-equiv′ : (A : Type ℓ) → is-equiv′ (id {A = A})
id-is-equiv′ _ .equiv-proof′ = strict-contr-fibers id

id-equiv′ : (A : Type ℓ) → A ≃′ A
id-equiv′ _ .fst = id
id-equiv′ A .snd = id-is-equiv′ A
