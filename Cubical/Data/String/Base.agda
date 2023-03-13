{-# OPTIONS --safe #-}
module Cubical.Data.String.Base where

open import Cubical.Data.Bool.Base
open import Cubical.Data.Char.Base
open import Cubical.Data.List.Base
open import Cubical.Foundations.Function

import Agda.Builtin.String as String

open String public using ( String )
  renaming
  ( primStringUncons   to uncons
  ; primStringToList   to toList
  ; primStringFromList to fromList
  ; primShowString     to show
  )

-- infix 4 _≈_
-- _≈_ : Rel String zero
-- _≈_ = Pointwise _≡_ on toList

-- -- Lexicographic ordering on Strings

-- infix 4 _<_
-- _<_ : Rel String zero
-- _<_ = Lex-< _≡_ Char._<_ on toList

-- infix 4 _≤_
-- _≤_ : Rel String zero
-- _≤_ = Lex-≤ _≡_ Char._<_ on toList

-- wordsByᵇ : (Char → Bool) → String → List String
-- wordsByᵇ p = map fromList ∘ List.wordsByᵇ p ∘ toList
