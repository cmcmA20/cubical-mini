{-# OPTIONS --safe #-}
module Foundations.Equiv.Base where

open import Foundations.Base
open import Foundations.HLevel.Base
open import Foundations.Path.Base

open import Foundations.Prim.Equiv public

-- include `equiv` or `_≃_` if the definition is about equivalences (`_≃_`)
-- include `is-equiv`       if the definition is about function being an equivalence (`is-equiv`)
-- use `ₑ` subscript for common operators on equivalences

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  f : A → B

_≃ᴱ_ : (A : Type ℓ) (B : Type ℓ′) → Type _
A ≃ᴱ B = Σ[ f ꞉ (A → B) ] is-equivᴱ f

is-equivᴱ→inverse : {A : Type ℓ} {@0 B : Type ℓ′} {@0 f : A → B} → is-equivᴱ f → (B → A)
is-equivᴱ→inverse eqv y = eqv y .fst .fst


_is-left-inverse-of_ : (B → A) → (A → B) → Type _
g is-left-inverse-of f = Π[ x ꞉ _ ] (g (f x) ＝ x)
retraction = _is-left-inverse-of_

_is-right-inverse-of_ : (B → A) → (A → B) → Type _
g is-right-inverse-of f = Π[ y ꞉ _ ] (f (g y) ＝ y)
section = _is-right-inverse-of_

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to is-contr (fibre f b).
strict-contr-fibres : (g : B → A) (b : B)
                    → Σ[ t        ꞉ fibre f (f (g b)) ]
                      Π[ (y′ , q) ꞉ fibre f       b   ]
                      Path (fibre f (f (g b))) t (g (f y′) , ap (f ∘ g) q)
strict-contr-fibres     g b .fst           = g b , refl
strict-contr-fibres {f} g b .snd (a , p) i = g (p (~ i)) , λ j → f (g (p (~ i ∨ j)))

id-is-equiv : is-equiv (id {A = A})
id-is-equiv .equiv-proof = strict-contr-fibres id

idₑ : A ≃ A
idₑ = id , id-is-equiv

equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
equiv-centre e y = e .snd .equiv-proof y .fst

equiv-path : (e : A ≃ B) (y : B) (v : fibre (e .fst) y) → equiv-centre e y ＝ v
equiv-path e y = e .snd .equiv-proof y .snd

opaque
  unfolding is-of-hlevel
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

instance
  H-Level-is-equiv : ∀ {n} → H-Level (suc n) (is-equiv f)
  H-Level-is-equiv = hlevel-prop-instance (is-equiv-is-prop _)

equiv-ext : {e₀ e₁ : A ≃ B} (h : e₀ .fst ＝ e₁ .fst) → e₀ ＝ e₁
equiv-ext {e₀} {e₁} h i = h i , is-prop→pathP (λ i → is-equiv-is-prop (h i)) (e₀ .snd) (e₁ .snd) i

is-equiv→inverse : {f : A → B} → is-equiv f → (B → A)
is-equiv→inverse eqv y = eqv .equiv-proof y .fst .fst

is-equiv→counit : (eqv : is-equiv f) (y : B) → f (is-equiv→inverse eqv y) ＝ y
is-equiv→counit eqv y = eqv .equiv-proof y .fst .snd

is-equiv→unit : (eqv : is-equiv f) (x : A) → is-equiv→inverse eqv (f x) ＝ x
is-equiv→unit {f} eqv x i = eqv .equiv-proof (f x) .snd (x , refl) i .fst

is-equiv→zig : (eqv : is-equiv f) (x : A)
             →  ap f (is-equiv→unit eqv x)
             ＝ is-equiv→counit eqv (f x)
is-equiv→zig {f} eqv x i j = hcomp (∂ i ∨ ∂ j) λ where
   k (i = i0) → f (is-equiv→unit eqv x j)
   k (i = i1) → is-equiv→counit eqv (f x) (j ∨ ~ k)
   k (j = i0) → is-equiv→counit eqv (f x) (i ∧ ~ k)
   k (j = i1) → f x
   k (k = i0) → eqv .equiv-proof (f x) .snd (x , refl) j .snd i

is-equiv→zag : (eqv : is-equiv f) (y : B)
             →  ap (is-equiv→inverse eqv) (is-equiv→counit eqv y)
             ＝ is-equiv→unit eqv (is-equiv→inverse eqv y)
is-equiv→zag {B} {f} eqv b =
  subst (λ b → ap g (ε b) ＝ η (g b)) (ε b) (helper (g b)) where
    g = is-equiv→inverse eqv
    ε = is-equiv→counit eqv
    η = is-equiv→unit eqv

    helper : ∀ a → ap g (ε (f a)) ＝ η (g (f a))
    helper a i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → g (ε (f a) (j ∨ ~ k))
      k (i = i1) → η (η a (~ k)) j
      k (j = i0) → g (is-equiv→zig eqv a (~ i) (~ k))
      k (j = i1) → η a (i ∧ ~ k)
      k (k = i0) → η a (i ∧ j)

@0 erased≃id : Erased A ≃ A
erased≃id .fst = erased
erased≃id .snd .equiv-proof = strict-contr-fibres (λ a → erase a)

module _ {ℓ̂ : I → Level} (P : (i : I) → Type (ℓ̂ i)) where

  private
    L = P i0
    R = P i1

    g = coei→1 P

  opaque
    transport-line-is-equiv : ∀ i → is-equiv (g i)
    transport-line-is-equiv i =
      coe1→i (λ j → is-equiv (g j)) i id-is-equiv

  transport-line-equiv : ∀ i → P i ≃ R
  transport-line-equiv i .fst = g i
  transport-line-equiv i .snd = transport-line-is-equiv i

  line→is-equiv : is-equiv (g i0)
  line→is-equiv = transport-line-is-equiv i0

  line→equiv : L ≃ R
  line→equiv = transport-line-equiv i0
