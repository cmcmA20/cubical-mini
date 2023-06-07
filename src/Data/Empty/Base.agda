{-# OPTIONS --safe #-}
module Data.Empty.Base where

open import Foundations.Base

data ⊥ : Type where

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 B : Type ℓ′

rec : @0 ⊥ → A
rec ()

rec′ : @irr ⊥ → A
rec′ ()

absurd = rec

elim : {@0 A : ⊥ → Type ℓ} → (@0 x : ⊥) → A x
elim ()

⊥-is-prop : is-prop ⊥
⊥-is-prop ()

absurd-is-contr : is-contr (⊥ → A)
absurd-is-contr .fst ()
absurd-is-contr .snd _ _ ()

absurd-path : {y : A} {@0 x : ⊥} → absurd x ＝ y
absurd-path {x = ()}

data ⊥ω : Typeω where

⊥→⊥ω : ⊥ → ⊥ω
⊥→⊥ω ()

recω : {@0 A : Typeω} → @0 ⊥ω → A
recω ()

recω′ : {@0 A : Typeω} → @irr ⊥ω → A
recω′ ()

elimω : {@0 A : ⊥ω → Typeω} → (@0 x : ⊥ω) → A x
elimω ()
