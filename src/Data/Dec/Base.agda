{-# OPTIONS --safe #-}
module Data.Dec.Base where

open import Foundations.Base

open import Correspondences.Erased

import Data.Bool.Base as Bool
open Bool using (Bool; false; true; not; if_then_else_; ⟦_⟧ᵇ)
import      Data.Empty.Base as ⊥
open ⊥ using (⊥; ¬_)

private variable
  ℓ ℓ′ ℓ″ : Level
  P : Type ℓ
  Q : Type ℓ′
  a b : Bool

-- there is a class of types that can be reflected in booleans
module Reflects′ where

  data Reflects⁰ {ℓ} (P : Type ℓ) : Bool → Type ℓ where
    ofʸ : ( p :   P) → Reflects⁰ P true
    ofⁿ : (¬p : ¬ P) → Reflects⁰ P false

  of : if b then P else ¬ P → Reflects⁰ P b
  of {b = false} ¬p = ofⁿ ¬p
  of {b = true }  p = ofʸ p

  invert : Reflects⁰ P b → if b then P else ¬ P
  invert (ofʸ  p) = p
  invert (ofⁿ ¬p) = ¬p

  ¬-reflects : Reflects⁰ P b → Reflects⁰ (¬ P) (not b)
  ¬-reflects (ofʸ  p) = ofⁿ (_$ p)
  ¬-reflects (ofⁿ ¬p) = ofʸ ¬p

  reflects-det : Reflects⁰ P a → Reflects⁰ P b → a ＝ b
  reflects-det (ofʸ  p) (ofʸ  p′) = refl
  reflects-det (ofʸ  p) (ofⁿ ¬p′) = ⊥.rec (¬p′ p)
  reflects-det (ofⁿ ¬p) (ofʸ  p′) = ⊥.rec (¬p p′)
  reflects-det (ofⁿ ¬p) (ofⁿ ¬p′) = refl

  map : (P → Q) → (¬ P → ¬ Q) → Reflects⁰ P b → Reflects⁰ Q b
  map to fro (ofʸ  p) = ofʸ (to p)
  map to fro (ofⁿ ¬p) = ofⁿ (fro ¬p)

open Reflects′ public
  using (Reflects⁰; ofʸ; ofⁿ)


-- witness of a predicate being (already) decided
infix 2 _because_
record Dec {ℓ} (P : Type ℓ) : Type ℓ where
  constructor _because_
  field
    does  : Bool
    proof : Reflects⁰ P does
open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

elim : {C : Dec P → Type ℓ′}
         → (( p :   P) → C (yes p))
         → ((¬p : ¬ P) → C (no ¬p))
         → (d : Dec P) → C d
elim y n (no ¬p) = n ¬p
elim y n (yes p) = y p

elim² : {C : Dec P → Dec Q → Type ℓ″}
      → (( p :   P) → ( q :   Q) → C (yes p) (yes q))
      → (( p :   P) → (¬q : ¬ Q) → C (yes p) (no ¬q))
      → ((¬p : ¬ P) → ( q :   Q) → C (no ¬p) (yes q))
      → ((¬p : ¬ P) → (¬q : ¬ Q) → C (no ¬p) (no ¬q))
      → (p : Dec P) → (q : Dec Q) → C p q
elim² yy yn ny nn (no ¬p) (no ¬q) = nn ¬p ¬q
elim² yy yn ny nn (no ¬p) (yes q) = ny ¬p q
elim² yy yn ny nn (yes p) (no ¬q) = yn p ¬q
elim² yy yn ny nn (yes p) (yes q) = yy p q

map : (P → Q) → (¬ P → ¬ Q) → Dec P → Dec Q
map to fro dec .does  = dec .does
map to fro dec .proof = Reflects′.map to fro (dec .proof)

recover : Dec P → ∥ P ∥ᴱ → P
recover (yes p) _  = p
recover (no ¬p) ∣ 0p ∣ᴱ = ⊥.rec (¬p 0p)

recover′ : Dec P → @irr P → P
recover′ (yes p) _ = p
recover′ (no ¬p) p = ⊥.rec′ (¬p p)

rec : (P → Q) → (¬ P → Q) → Dec P → Q
rec ifyes ifno (yes p) = ifyes p
rec ifyes ifno (no ¬p) = ifno ¬p

⌊_⌋ : Dec P → Bool
⌊ b because _ ⌋ = b

is-true : Dec P → Type
is-true = ⟦_⟧ᵇ ∘ ⌊_⌋
