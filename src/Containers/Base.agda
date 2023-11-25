{-# OPTIONS --safe #-}
module Containers.Base where

open import Foundations.Base
open import Foundations.Equiv.Base

open import Meta.Idiom

infix 5 _▶_
record Container (s p : Level) : Type (ℓsuc (s ⊔ p)) where
  constructor _▶_
  field
    Shape    : Type s
    Position : Shape → Type p

open Container public

private variable
  ℓ ℓ′ s s′ p p′ : Level
  X  : Type ℓ
  C  : Container s p
  C′ : Container s′ p′

⟦_⟧ : Container s p → Type ℓ → Type (ℓ ⊔ (s ⊔ p))
⟦ S ▶ P ⟧ X = Σ[ s ꞉ S ] (P s → X)

_∈_ : {S : Type s} {P : S → Type p}
    → X → ⟦ S ▶ P ⟧ X → Type (level-of-type X ⊔ p)
x ∈ xs = fibre (xs .snd) x

_∈!_ : {S : Type s} {P : S → Type p}
     → X → ⟦ S ▶ P ⟧ X → Type (level-of-type X ⊔ p)
x ∈! xs = is-contr (x ∈ xs)

map : {C : Container s p} {X : Type ℓ} {Y : Type ℓ′}
    → (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f (x , g) = x , f ∘ g

instance
  Map-Container : ∀ {s p} {C : Container s p} → Map (eff ⟦ C ⟧)
  Map-Container .Map._<$>_ = map


-- container morphism
record _⇒_ (C : Container s p) (C′ : Container s′ p′)
           : Type (s ⊔ p ⊔ s′ ⊔ p′) where
  constructor _▶_
  field
    shape    : Shape C → Shape C′
    position : ∀ {sh} → Position C′ (shape sh) → Position C sh

  ⟪_⟫→ : ⟦ C ⟧ X → ⟦ C′ ⟧ X
  ⟪ x , g ⟫→ = shape x , g ∘ position

open _⇒_ public


-- Linear/cartesian container morphism
record _⊸_ (C : Container s p) (C′ : Container s′ p′)
  : Type (s ⊔ p ⊔ s′ ⊔ p′) where
  field
    shape⊸    : Shape C → Shape C′
    position⊸ : ∀ {sh} → Position C′ (shape⊸ sh) ≃ Position C sh

  morphism : C ⇒ C′
  morphism .shape    = shape⊸
  morphism .position = position⊸ .fst

  ⟪_⟫⊸ : ⟦ C ⟧ X → ⟦ C′ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫→

open _⊸_ public using (shape⊸; position⊸; ⟪_⟫⊸)
