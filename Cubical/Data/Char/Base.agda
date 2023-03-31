{-# OPTIONS --safe #-}
module Cubical.Data.Char.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary.Negation

open import Agda.Builtin.Char public using ( Char )
  renaming
  -- testing
  ( primIsLower    to isLower
  ; primIsDigit    to isDigit
  ; primIsAlpha    to isAlpha
  ; primIsSpace    to isSpace
  ; primIsAscii    to isAscii
  ; primIsLatin1   to isLatin1
  ; primIsPrint    to isPrint
  ; primIsHexDigit to isHexDigit
  -- transforming
  ; primToUpper to toUpper
  ; primToLower to toLower
  -- converting
  ; primCharToNat to toℕ
  ; primNatToChar to fromℕ
  )

open import Agda.Builtin.String using (primShowChar) public

infix 4 _≈_ _≉_
_≈_ : Rel Char Char _
c₁ ≈ c₂ = toℕ c₁ ≡ toℕ c₂

_≉_ : Rel Char Char _
c₁ ≉ c₂ = ¬ (c₁ ≈ c₂)

-- infix 4 _≈ᵇ_
-- _≈ᵇ_ : (c d : Char) → Bool
-- c ≈ᵇ d = toℕ c ℕ.≡ᵇ toℕ d

-- infix 4 _<_
-- _<_ : Rel Char zero
-- _<_ = ℕ._<_ on toℕ

-- infix 4 _≤_
-- _≤_ : Rel Char zero
-- _≤_ = ReflClosure _<_
