{-# OPTIONS --safe #-}
module Foundations.Equiv where

open import Foundations.Prelude

private variable ℓ ℓ′ ℓ″ ℓ‴ : Level

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

-- id-eq : A ≃ A
-- id-eq .forward = id
-- id-eq .backward = id
-- id-eq .R x y = x ＝ y
-- id-eq .forward-prop  x (a₁ , p₁) (a₂ , p₂) = cong₂ _,_ (sym p₁ ∙ p₂    ) {!!}
-- id-eq .backward-prop y (b₁ , q₁) (b₂ , q₂) = cong₂ _,_ (q₁     ∙ sym q₂) {!!}

-- -- id-eq .R x y = x ＝ y
-- -- id-eq .forward  x = (x , refl) , λ z i → z .snd i     , λ j → z .snd (   i ∧   j)
-- -- id-eq .backward x = (x , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ (i ∧ ~ j))
--
-- -- id-eq : A ≃ A
-- -- id-eq .R x y = x ＝ y
-- -- id-eq .forward  x = (x , refl) , λ z i → z .snd i     , λ j → z .snd (   i ∧   j)
-- -- id-eq .backward x = (x , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ (i ∧ ~ j))

-- -- module _ (e : A ≃ B) where
--
-- --   to : A → B
-- --   to x = e .forward x .fst .fst
--
-- --   from : B → A
-- --   from y = e .backward y .fst .fst
--
-- --   from-to : (x : A) → from (to x) ＝ x
-- --   from-to x i = e .backward (to x) .snd (x , e .forward x .fst .snd) i .fst
--
-- --   to-from : (y : B) → to (from y) ＝ y
-- --   to-from y i = e .forward (from y) .snd (y , e .backward y .fst .snd) i .fst
--
-- --   -- to-is-equiv′ : is-equiv′ to
-- --   -- to-is-equiv′ .is-equiv′.is-eqv′ y = (from y , to-from y)
-- --   --   , λ z i → let w = from-to (from y) in {!!} , {!!}
--
-- --   -- equiv′ : A ≃′ B
-- --   -- equiv′ = to , to-is-equiv′
--
-- comp-eq : A ≃ B → B ≃ C → A ≃ C
-- comp-eq e e′ .forward x = e′ .forward (e .forward x)
-- comp-eq e e′ .backward z = e .backward (e′ .backward z)
-- comp-eq e e′ .R x z = Σ[ y ꞉ _ ] Σ[ _ ꞉ e .R x y ] (e′ .R y z)
-- comp-eq e e′ .forward-prop x (c₁ , b₁ , r₁ , r₁′) (c₂ , b₂ , r₂ , r₂′) = {!!}
-- comp-eq e e′ .backward-prop = {!!}

-- qwe : (e : A ≃ B)
--     → comp-eq e id-eq ＝ e
-- qwe e i .R x y = let z = e .forward-prop x (y , {!e .forward x .fst .fst!}) in {!!}
-- qwe e i .forward = {!!}
-- qwe e i .backward = {!!}
