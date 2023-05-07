{-# OPTIONS --safe #-}
module Foundations.Equiv where

open import Prim.Equiv
open import Foundations.Prelude
open import Foundations.HLevel
open import Foundations.Path

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A A′ A″ : Type ℓ
  B B′ B″ : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴

infix 8 _≃_
record _≃_ (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′)

is-inv : {A : Type ℓ} {B : Type ℓ′} → (A → B) → (B → A) → Type (ℓ ⊔ ℓ′)
is-inv {A} {B} f g = (a : A) (b : B) → (a ＝ g b) ≃ (f a ＝ b)

record _≃_ A B where
  coinductive
  field
    to   : A → B
    from : B → A
    equiv-proof : is-inv to from
open _≃_ public

-- reimplement using raw `transp`?
down : A ＝ B → A ≃ B
down p .to   = transport p
down p .from = transport (sym p)
down p .equiv-proof x x′ = down
  $ sym (PathP＝Path⁻ (λ i → p i) x x′)
  ∙      PathP＝Path  (λ i → p i) x x′

idₑ : A ≃ A
idₑ .to   = id
idₑ .from = id
idₑ .equiv-proof _ _ = idₑ

infixr 29 _∙ₑ_
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
(f ∙ₑ g) .to   = g .to   ∘ f .to
(f ∙ₑ g) .from = f .from ∘ g .from
(f ∙ₑ g) .equiv-proof x z =
  let le = f .equiv-proof        x  (g .from z)
      ri = g .equiv-proof (f .to x)          z
  in le ∙ₑ ri

left-unital  : (f : A ≃ B) → idₑ ∙ₑ f   ＝ f
left-unital f _ .to   = f .to
left-unital f _ .from = f .from
left-unital f i .equiv-proof x y = left-unital (f .equiv-proof x y) i

right-unital : (f : A ≃ B) → f ∙ₑ idₑ ＝ f
right-unital f _ .to   = f .to
right-unital f _ .from = f .from
right-unital f i .equiv-proof x y = right-unital (f .equiv-proof x y) i

assoc : (f : A ≃ B) (g : B ≃ C) (h : C ≃ D) → (f ∙ₑ g) ∙ₑ h ＝ f ∙ₑ (g ∙ₑ h)
assoc f g h _ .to   = h .to   ∘ g .to   ∘ f .to
assoc f g h _ .from = f .from ∘ g .from ∘ h .from
assoc f g h i .equiv-proof x w =
  let le = f .equiv-proof               x   (g .from (h .from w))
      mi = g .equiv-proof        (f .to x)           (h .from w)
      ri = h .equiv-proof (g .to (f .to x))                   w
  in assoc le mi ri i

whisker : A′ ＝ A → A ≃ B → B ＝ B′
        → A′          ≃          B′
whisker p e q = down p ∙ₑ e ∙ₑ down q

-- univalence awaits
zero-preservation : down {ℓ} {A} refl ＝ idₑ
zero-preservation i .to   x = transport-refl x i
zero-preservation i .from x = transport-refl x i
zero-preservation {A} i .equiv-proof x y = {!!}
--   in subst (λ focus → down focus ＝ {!!}) {!!} {!!} i
-- subst (λ focus → down focus ＝ idₑ) (sym (∙-inv-l refl)) what-is-this i

-- funny one, provable both with univalence and with K
-- but is it really independent and provable using only cubical ops?
-- I think there's a unique term of this type, isn't it related to some parametricity stuff?
mirror : {x y : A} → (x ＝ y) ＝ (y ＝ x)
mirror = {!!}

-- what the hell is this?
swap : {x y : A} {z w : B} → (x ＝ y) ＝ (z ＝ w) → (w ＝ z) ＝ (y ＝ x)
swap p = sym $ mirror ◁ p ▷ mirror

swapₑ : {A B : Type ℓ} {x y : A} {z w : B} → (x ＝ y) ≃ (z ＝ w) → (w ＝ z) ≃ (y ＝ x)
swapₑ e .to   = sym ∘ e .from ∘ sym
swapₑ e .from = sym ∘ e .to   ∘ sym
swapₑ e .equiv-proof p q =
  let t = e .equiv-proof (sym q) (sym p)
  in swapₑ $ {!!} -- need something like `cong-equiv`

swapₑ-invol : {x y : A} {z w : B} (f : (x ＝ y) ≃ (z ＝ w)) → swapₑ (swapₑ f) ＝ f
swapₑ-invol f _ .to   = f .to
swapₑ-invol f _ .from = f .from
swapₑ-invol f i .equiv-proof p q = let t = f .equiv-proof p q in {!!}

-- note the flip
inv : {A B : Type ℓ} → A ≃ B → B ≃ A
inv e .to   = e .from
inv e .from = e .to
inv e .equiv-proof y x = swapₑ $ e .equiv-proof x y

involution : (e : A ≃ B) → inv (inv e) ＝ e
involution e _ .to   = e .to
involution e _ .from = e .from
involution e i .equiv-proof x y = swapₑ-invol (e .equiv-proof x y) i

cancel : (e : A ≃ B) → e ∙ₑ inv e ＝ idₑ
cancel e i .to   x = e .equiv-proof x (e .to x) .from refl (~ i)
cancel e i .from x = e .equiv-proof x (e .to x) .from refl (~ i)
cancel e i .equiv-proof x y = {!!} -- no idea, probably need univalence again

equiv-ext : (f g : A ≃ B) → (f .to ＝ g .to) → (f .from ＝ g .from) → f ＝ g
equiv-ext _ _ p _ i .to   = p i
equiv-ext _ _ _ q i .from = q i
equiv-ext f g p q i .equiv-proof x y = {!!}

vert : (f : A ≃ B) (g : A′ ≃ B′) (h : A″ ≃ B″)
       (p : A ＝ A′) (q : B ＝ B′) (r : A′ ＝ A″) (s : B′ ＝ B″)
       (α : f ∙ₑ down q ＝ down p ∙ₑ g)
       (β : g ∙ₑ down s ＝ down r ∙ₑ h)
     → f ∙ₑ down (q ∙ s) ＝ down (p ∙ r) ∙ₑ h
vert f g h p q r s α β = {!!}
