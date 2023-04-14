{-# OPTIONS --safe #-}
module Foundations.Equiv where

open import Foundations.Prelude
open import Foundations.HLevel

private variable ℓ ℓ′ ℓ″ ℓ‴ : Level

-- courtesy of Mike Shulman
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

-- definitionally involutive
inv-eq-invol : {e : A ≃ B} → inv-eq (inv-eq e) ＝ e
inv-eq-invol = refl

-- TODO
-- how to make the composition definitionally associative and unital?

-- id-eq : A ≃ A
-- id-eq .forward  = id
-- id-eq .backward = id
-- id-eq .R x y = x ＝ y
-- id-eq .forward-prop  x u v = let z = Singleton in {!!}
-- id-eq .backward-prop y u v = let z = SingletonP-is-contr in Σ-PathP {!!} {!!}

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

-- comp-eq : A ≃ B → B ≃ C → A ≃ C
-- comp-eq e e′ .forward  = e′ .forward  ∘ e  .forward
-- comp-eq e e′ .backward = e  .backward ∘ e′ .backward
-- comp-eq e e′ .R x z = Σ[ y ꞉ _ ] (e .R x y) × (e′ .R y z)
-- comp-eq e e′ .forward-prop x (c₁ , b₁ , r₁ , r₁′) (c₂ , b₂ , r₂ , r₂′) = {!!}
-- comp-eq e e′ .backward-prop = {!!}



idₑ : A ≃ A
idₑ .forward  = id
idₑ .backward = id
idₑ .R x y = x ＝ y
idₑ .forward-prop  x = is-contr→is-prop (Singleton-is-contr (x , refl))
idₑ .backward-prop y = is-contr→is-prop ((y , refl) , λ t → let zz = Singleton-is-prop in {!!})

comp-eq : A ≃ B → B ≃ C → A ≃ C
comp-eq e e′ .forward = e′ .forward ∘ e .forward
comp-eq e e′ .backward = e .backward ∘ e′ .backward
comp-eq e e′ .R x z = e .R x (e .forward x) × e′ .R (e′ .backward z) z
comp-eq e e′ .forward-prop = {!!}
comp-eq e e′ .backward-prop = {!!}

infixr 29 _∙ₑ_
_∙ₑ_ = comp-eq

kekw : (e : B ≃ C) (y : B) (z : C) → (y ＝ y) × e .R (e .backward z) z
kekw e y z = refl , let tt = inhabited-prop-is-contr {!!} {!!} in tt .fst

unital-left : (e : B ≃ C) → idₑ ∙ₑ e ＝ e
unital-left e i = record
                    { forward = e .forward
                    ; backward = e .backward
                    ; R = λ y z → {!!}
                    ; forward-prop = {!!}
                    ; backward-prop = {!!}
                    }

-- A ≃ B , B ≃ C , C ≃ D
-- R₁₂ x z = (y : B) × (R₁ x y × R₂ y z)
-- R₂₃ y w = (z : C) × (R₂ y z × R₃ z w)

-- R₁₋₂₃ x w = (y : B) × (R₁ x y × (z : C) × (R₂ y z × R₃ z w))
-- R₁₂₋₃ x w = (z : C) × ((y : B) × (R₁ x y × R₂ y z) × R₃ z w)

-- qwe : (e : A ≃ B)
--     → comp-eq e id-eq ＝ e
-- qwe e i .R x y = let z = e .forward-prop x (y , {!e .forward x .fst .fst!}) in {!!}
-- qwe e i .forward = {!!}
-- qwe e i .backward = {!!}
