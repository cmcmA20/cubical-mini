{-# OPTIONS --safe #-}
module Foundations.Equiv.Base where

open import Prim.Equiv public
open import Foundations.Prelude

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to is-contr (fibre f b).
strict-contr-fibers : {f : A → B} (g : B → A) (b : B)
                    → Σ[ t  ꞉ fibre f (f (g b)) ]
                      Π[ t′ ꞉ fibre f       b   ]
                      Path (fibre f (f (g b))) t (g (f (t′ .fst)) , cong (f ∘ g) (t′ .snd))
strict-contr-fibers     g b .fst = g b , refl
strict-contr-fibers {f} g b .snd (a , p) i = g (p (~ i)) , λ j → f (g (p (~ i ∨ j)))

-- The identity equivalence
id-is-equiv : (A : Type ℓ) → is-equiv (id {A = A})
id-is-equiv _ .equiv-proof = strict-contr-fibers id

idₑ : (A : Type ℓ) → A ≃ A
idₑ _ .fst = id
idₑ A .snd = id-is-equiv A

equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
equiv-centre e y = e .snd .equiv-proof y .fst

equiv-path : (e : A ≃ B) (y : B) (v : fibre (e .fst ) y) → equiv-centre e y ＝ v
equiv-path e y = e .snd .equiv-proof y .snd

is-equiv-is-prop : (f : A → B) → is-prop (is-equiv f)
is-equiv-is-prop f p q i .equiv-proof y =
  let p₂ = p .equiv-proof y .snd
      q₂ = q .equiv-proof y .snd
  in p₂ (q .equiv-proof y .fst) i , λ w j → hcomp (∂ i ∨ ∂ j) λ where
     k (i = i0) → p₂ w j
     k (i = i1) → q₂ w (j ∨ ~ k)
     k (j = i0) → p₂ (q₂ w (~ k)) i
     k (j = i1) → w
     k (k = i0) → p₂ w (i ∨ j)

equiv→inverse : {f : A → B} → is-equiv f → (B → A)
equiv→inverse eqv y = eqv .equiv-proof y .fst .fst

equiv→counit : {f : A → B} (eqv : is-equiv f) (y : B) → f (equiv→inverse eqv y) ＝ y
equiv→counit eqv y = eqv .equiv-proof y .fst .snd

equiv→unit : {f : A → B} (eqv : is-equiv f) (x : A) → equiv→inverse eqv (f x) ＝ x
equiv→unit {f} eqv x i = eqv .equiv-proof (f x) .snd (x , refl) i .fst

equiv→zig
  : {f : A → B} (eqv : is-equiv f) (x : A)
  → ap f (equiv→unit eqv x) ＝ equiv→counit eqv (f x)
equiv→zig {f = f} eqv x i j = hcomp (∂ i ∨ ∂ j) λ where
   k (i = i0) → f (equiv→unit eqv x j)
   k (i = i1) → equiv→counit eqv (f x) (j ∨ ~ k)
   k (j = i0) → equiv→counit eqv (f x) (i ∧ ~ k)
   k (j = i1) → f x
   k (k = i0) → eqv .equiv-proof (f x) .snd (x , refl) j .snd i

equiv→zag
  : {f : A → B} (eqv : is-equiv f) (y : B)
  → ap (equiv→inverse eqv) (equiv→counit eqv y) ＝ equiv→unit eqv (equiv→inverse eqv y)
equiv→zag {f} eqv b =
  subst (λ b → ap g (ε b) ＝ η (g b)) (ε b) (helper (g b)) where
  g = equiv→inverse eqv
  ε = equiv→counit eqv
  η = equiv→unit eqv

  helper : ∀ a → ap g (ε (f a)) ＝ η (g (f a))
  helper a i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → g (ε (f a) (j ∨ ~ k))
    k (i = i1) → η (η a (~ k)) j
    k (j = i0) → g (equiv→zig eqv a (~ i) (~ k))
    k (j = i1) → η a (i ∧ ~ k)
    k (k = i0) → η a (i ∧ j)

-- equivEq : {e f : A ≃ B} → (h : e .fst ＝ f .fst) → e ＝ f
-- equivEq {e = e} {f = f} h = λ i → (h i) , is-prop→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i
