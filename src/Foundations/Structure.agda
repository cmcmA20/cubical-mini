{-# OPTIONS --safe #-}
module Foundations.Structure where

open import Prim.Equiv public

open import Foundations.Prelude

private variable
  ℓ ℓ′ ℓ″ : Level
  S : Type ℓ → Type ℓ′

-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X,
-- the pair (X , s) : TypeWithStr ℓ S means that X is equipped with a S-structure, witnessed by s.

Type-with-str : (ℓ : Level) (S : Type ℓ → Type ℓ′) → Type (ℓsuc ℓ ⊔ ℓ′)
Type-with-str ℓ S = Σ[ X ꞉ Type ℓ ] S X

type : Type-with-str ℓ S → Type ℓ
type = fst

str : (A : Type-with-str ℓ S) → S (type A)
str = snd

⟨_⟩ : Type-with-str ℓ S → Type ℓ
⟨_⟩ = type

instance
  mk-type-with-str : {X : Type ℓ} → ⦃ S X ⦄ → Type-with-str ℓ S
  mk-type-with-str ⦃ (s) ⦄ = _ , s

-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι : StrEquiv S ℓ'
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ″
Str-equiv : (S : Type ℓ → Type ℓ″) (ℓ′ : Level) → Type (ℓsuc (ℓ ⊔ ℓ′) ⊔ ℓ″)
Str-equiv {ℓ} S ℓ′ = (A B : Type-with-str ℓ S) → type A ≃′ type B → Type ℓ′

-- An S-structure may instead be equipped with an action on equivalences, which will
-- induce a notion of S-homomorphism

-- TODO wait for proper equivalences
Equiv-action : (S : Type ℓ → Type ℓ″) → Type (ℓsuc ℓ ⊔ ℓ″)
Equiv-action {ℓ} S = {X Y : Type ℓ} → X ≃′ Y → S X ≃′ S Y

Equiv-action→Str-equiv : {S : Type ℓ → Type ℓ″}
  → Equiv-action S → Str-equiv S ℓ″
Equiv-action→Str-equiv α (X , s) (Y , t) e = equiv-forward′ (α e) s ＝ t
