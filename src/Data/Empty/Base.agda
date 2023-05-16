{-# OPTIONS --safe #-}
module Data.Empty.Base where

open import Foundations.Base
open import Foundations.Equiv

data ⊥ : Type where

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 B : Type ℓ′

rec : @0 ⊥ → A
rec ()

elim : {@0 A : ⊥ → Type ℓ} → (@0 x : ⊥) → A x
elim ()

⊥-is-prop : is-prop ⊥
⊥-is-prop ()

absurd-is-contr : is-contr (⊥ → A)
absurd-is-contr .fst ()
absurd-is-contr .snd _ _ ()

uninhab-Equiv : {A : Type ℓ} {B : Type ℓ′} → (A → ⊥) → (B → ⊥) → A ≃ B
uninhab-Equiv {A} {B} ¬a ¬b = Iso→Equiv 𝔯
  where
  𝔯 : A ≅ B
  𝔯 .fst a = rec (¬a a)
  𝔯 .snd .is-iso.inv b = rec (¬b b)
  𝔯 .snd .is-iso.rinv b = rec (¬b b)
  𝔯 .snd .is-iso.linv a = rec (¬a a)

⊥* : Type ℓ
⊥* {ℓ} = Lift ℓ ⊥

rec* : @0 ⊥* {ℓ′} → A
rec* ()

elim* : {@0 A : ⊥* {ℓ} → Type ℓ′} → (@0 x : ⊥*) → A x
elim* ()


data ⊥ω : Typeω where

⊥→⊥ω : ⊥ → ⊥ω
⊥→⊥ω ()

recω : {@0 A : Typeω} → @0 ⊥ω → A
recω ()

elimω : {@0 A : ⊥ω → Typeω} → (@0 x : ⊥ω) → A x
elimω ()
