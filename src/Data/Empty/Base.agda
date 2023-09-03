{-# OPTIONS --safe #-}
module Data.Empty.Base where

open import Foundations.Base
open import Foundations.HLevel.Base

data ⊥ : Type where

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 x y : ⊥
  @0 Aω : Typeω
  n : HLevel

rec : @0 ⊥ → A
rec ()

rec′ : @irr ⊥ → A
rec′ ()

absurd = rec

elim : {@0 A : ⊥ → Type ℓ} → (@0 x : ⊥) → A x
elim ()

⊥-ext : x ＝ y
⊥-ext {x = ()}

opaque
  unfolding is-of-hlevel
  instance
    ⊥-is-prop : is-prop ⊥
    ⊥-is-prop ()

  absurd-is-contr : is-contr (⊥ → A)
  absurd-is-contr .fst ()
  absurd-is-contr .snd _ _ ()

⊥-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) ⊥
⊥-is-of-hlevel _ = is-prop→is-of-hlevel-suc ⊥-is-prop

absurd-path : {@0 y : A} {@0 x : ⊥} → absurd x ＝ y
absurd-path {x = ()}

data ⊥ω : Typeω where

⊥→⊥ω : ⊥ → ⊥ω
⊥→⊥ω ()

recω : @0 ⊥ω → A
recω ()

recω-irr : @irr ⊥ω → A
recω-irr ()

elimω : {@0 A : ⊥ω → Typeω} → (@0 x : ⊥ω) → A x
elimω ()

infixr 0 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

opaque
  unfolding is-of-hlevel
  ¬-is-prop : is-prop (¬ A)
  ¬-is-prop ¬a₁ ¬a₂ i a = ⊥-ext {x = ¬a₁ a} {y = ¬a₂ a} i


¬-is-of-hlevel : {A : Type ℓ} (n : HLevel) → is-of-hlevel (suc n) (¬ A)
¬-is-of-hlevel _ = is-prop→is-of-hlevel-suc ¬-is-prop

infix 4 _≠_
_≠_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≠ y = ¬ x ＝ y
