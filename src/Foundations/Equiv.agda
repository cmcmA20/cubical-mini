{-# OPTIONS --safe #-}
module Foundations.Equiv where

open import Prim.Equiv
open import Foundations.Prelude
-- open import Foundations.HLevel
open import Foundations.Path

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A A′ : Type ℓ
  B B′ : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴

infix 8 _≃_
record _≃_ (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′)

is-inv : {A : Type ℓ} {B : Type ℓ′} → (A → B) → (B → A) → Type (ℓ ⊔ ℓ′)
is-inv {A} {B} f g = Π[ a ꞉ A ] Π[ b ꞉ B ] (f a ＝ b) ≃ (a ＝ g b)

record _≃_ A B where
  coinductive
  field
    to   : A → B
    from : B → A
    equiv-proof : is-inv to from
open _≃_ public

down : A ＝ B → A ≃ B
down p .to   = transport p
down p .from = transport (sym p)
down p .equiv-proof x x′ = down
  $ sym (PathP＝Path  (λ i → p i) x x′)
  ∙      PathP＝Path⁻ (λ i → p i) x x′

-- univalence
-- up : A ≃ B → A ＝ B
-- up e = {!!}

idₑ : A ≃ A
idₑ .to = id
idₑ .from = id
idₑ .equiv-proof _ _ = idₑ

infixr 29 _∙ₑ_
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
(f ∙ₑ g) .to   = g .to   ∘ f .to
(f ∙ₑ g) .from = f .from ∘ g .from
(f ∙ₑ g) .equiv-proof x z =
  let le = g .equiv-proof (f .to x) z
      ri = f .equiv-proof x (g .from z)
  in le ∙ₑ ri

left-unital  : (f : A ≃ B) → idₑ ∙ₑ f   ＝ f
right-unital : (f : A ≃ B) → f   ∙ₑ idₑ ＝ f

left-unital f _ .to   = f .to
left-unital f _ .from = f .from
left-unital f i .equiv-proof x y = right-unital (f .equiv-proof x y) i

right-unital f _ .to   = f .to
right-unital f _ .from = f .from
right-unital f i .equiv-proof x y = left-unital (f .equiv-proof x y) i

assoc : (f : A ≃ B) (g : B ≃ C) (h : C ≃ D) → (f ∙ₑ g) ∙ₑ h ＝ f ∙ₑ (g ∙ₑ h)
assoc f g h i .to   = h .to   ∘ g .to   ∘ f .to
assoc f g h i .from = f .from ∘ g .from ∘ h .from
assoc f g h i .equiv-proof x w =
  let le = f .equiv-proof x (g .from (h .from w))
      mi = g .equiv-proof (f .to x) (h .from w)
      ri = h .equiv-proof (g .to (f .to x)) w
  in assoc ri mi le (~ i)

-- whisker : A′ ＝ A → A ≃ B → B ＝ B′ → A′ ≃ B′
-- whisker p e q .to   = transport q       ∘ e .to   ∘ transport p
-- whisker p e q .from = transport (sym p) ∘ e .from ∘ transport (sym q)
-- whisker p e q .equiv-proof x′ y′ =
--   whisker {!!} (e .equiv-proof (transport p x′) (transport (sym q) y′)) {!!}

example : {x y : A} (p : x ＝ y)
        →   x  ̇      p       ̇ y
                ┌─────────┐ _
                │    _    │
            p   │    _    │   sym p
                │    _    │ _
                └─────────┘
            y  ̇    sym p     ̇ x
example p = to-PathP (transport-path p p (sym p) ∙ ∙-cancel-l p (sym p))

-- wtf : {x y : A} → (x ＝ y) ＝ (y ＝ x)
-- wtf = {!!}

-- inv : {A B : Type ℓ} → A ≃ B → B ≃ A
-- inv e .to   = e .from
-- inv e .from = e .to
-- inv e .equiv-proof y x =
--   let w = up $ e .equiv-proof x y
--       p = e .equiv-proof (e .from y) y .from refl
--       q = e. equiv-proof x (e .to x) .to refl
--   in down $ {!!} ◁ sym w ▷ {!!}

-- involution : (e : A ≃ B) → inv (inv e) ＝ e
-- involution e _ .to   = e .to
-- involution e _ .from = e .from
-- involution e i .equiv-proof = {!!} -- e .equiv-proof
