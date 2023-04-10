module Prelude.Equiv where

open import Prim.Type
open import Prim.Interval
open import Prim.Kan
open import Prim.Data.Sigma
open import Prim.Data.Pi

private variable ℓ ℓ′ ℓ″ ℓ‴ : Level

is-contr : Type ℓ → Type ℓ
is-contr A = Σ[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y)

is-prop : Type ℓ → Type ℓ
is-prop A = Π[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y)

fibre : {A : Type ℓ} {B : Type ℓ′} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ′)
fibre {A = A} f y = Σ[ x ꞉ A ] (f x ＝ y)

record is-equiv′ {A : Type ℓ} {B : Type ℓ′} (f : A → B) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field is-eqv′ : (y : B) → is-contr (fibre f y)

infix 4 _≃′_
_≃′_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
A ≃′ B = Σ (A → B) is-equiv′
{-# BUILTIN EQUIV _≃′_ #-}

infix 4 _≃_
record _≃_ {ℓ} (A : Type ℓ) (B : Type ℓ) : Type (ℓsuc ℓ) where
  eta-equality
  field
    forward  : A → B
    backward : B → A
    R : A → B → Type ℓ
    forward-prop  : Π[ x ꞉ A ] is-prop (Σ[ y ꞉ B ] R x y)
    backward-prop : Π[ y ꞉ B ] is-prop (Σ[ x ꞉ A ] R x y)
open _≃_ public

private variable
  A B C : Type ℓ

inv-eq : A ≃ B → B ≃ A
inv-eq e .forward       = e .backward
inv-eq e .backward      = e .forward
inv-eq e .R             = flip (e .R)
inv-eq e .forward-prop  = e .backward-prop
inv-eq e .backward-prop = e .forward-prop

inv-eq-invol : {e : A ≃ B} → inv-eq (inv-eq e) ＝ e
inv-eq-invol = refl

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x

id-eq : A ≃ A
id-eq .forward = id
id-eq .backward = id
id-eq .R x y = x ＝ y
id-eq .forward-prop  x (a₁ , p₁) (a₂ , p₂) i = {!!} , {!!}
id-eq .backward-prop y (b₁ , q₁) (b₂ , q₂) i = {!!}

-- id-eq .R x y = x ＝ y
-- id-eq .forward  x = (x , refl) , λ z i → z .snd i     , λ j → z .snd (   i ∧   j)
-- id-eq .backward x = (x , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ (i ∧ ~ j))

-- inv-eq : A ≃ B → B ≃ A
-- inv-eq e = record { R = flip (e .R)
--                   ; forward  = e .backward
--                   ; backward = e .forward }

-- inv-eq-invol : {A B : Type ℓ}
--                (e : A ≃ B) → inv-eq (inv-eq e) ＝ e
-- inv-eq-invol _ = refl

-- id-eq : A ≃ A
-- id-eq .R x y = x ＝ y
-- id-eq .forward  x = (x , refl) , λ z i → z .snd i     , λ j → z .snd (   i ∧   j)
-- id-eq .backward x = (x , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ (i ∧ ~ j))

-- record Lift {ℓi ℓj} (A : Type ℓi) : Type (ℓi ⊔ ℓj) where
--   constructor lift
--   field lower : A

-- module _ (e : A ≃ B) where

--   to : A → B
--   to x = e .forward x .fst .fst

--   from : B → A
--   from y = e .backward y .fst .fst

--   from-to : (x : A) → from (to x) ＝ x
--   from-to x i = e .backward (to x) .snd (x , e .forward x .fst .snd) i .fst

--   to-from : (y : B) → to (from y) ＝ y
--   to-from y i = e .forward (from y) .snd (y , e .backward y .fst .snd) i .fst

--   -- to-is-equiv′ : is-equiv′ to
--   -- to-is-equiv′ .is-equiv′.is-eqv′ y = (from y , to-from y)
--   --   , λ z i → let w = from-to (from y) in {!!} , {!!}

--   -- equiv′ : A ≃′ B
--   -- equiv′ = to , to-is-equiv′

comp-eq : A ≃ B → B ≃ C → A ≃ C
comp-eq e e′ .forward x = e′ .forward (e .forward x)
comp-eq e e′ .backward z = e .backward (e′ .backward z)
comp-eq e e′ .R x z = Σ[ y ꞉ _ ] Σ[ _ ꞉ e .R x y ] (e′ .R y z)
comp-eq e e′ .forward-prop x (c₁ , b₁ , r₁ , r₁′) (c₂ , b₂ , r₂ , r₂′) = {!!}
comp-eq e e′ .backward-prop = {!!}

-- comp-eq : A ≃ B
--         → B ≃ C
--         → A ≃ C
-- comp-eq e₁ e₂ .R x z = Σ[ y ꞉ _ ] Σ[ _ ꞉ e₁ .R x y ] (e₂ .R y z)
-- comp-eq e₁ e₂ .forward  x = (to   e₂ (to   e₁ x) , to   e₁ x , e₁ .forward  _ .fst .snd , e₂ .forward  _ .fst .snd)
--   , λ z i → {!!} , {!!} , {!!} , {!!}
-- comp-eq e₁ e₂ .backward z = (from e₁ (from e₂ z) , from e₂ z , e₁ .backward _ .fst .snd , e₂ .backward _ .fst .snd)
--   , λ z i → {!!} , {!!} , {!!} , {!!}

-- zz : (R : A → B → Type ℓ) → Π[ x ꞉ A ] Π[ y ꞉ B ] (R x y ＝ Σ[ y₁ ꞉ B ] Σ[ p₁ ꞉ R x y₁ ] (y₁ ＝ y))
-- zz R x y i = {!!}

-- qwe : (e : A ≃ B)
--     → comp-eq e id-eq ＝ e
-- qwe e i .R x y = {!!}
-- qwe e i .forward = {!!}
-- qwe e i .backward = {!!}
