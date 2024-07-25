{-# OPTIONS --safe #-}
module Meta.Literals.FromString where

open import Foundations.Base

open import Data.String.Base
open import Data.Unit.Base

open import Agda.Builtin.FromString public
  using ()
  renaming ( IsString to From-string
           ; fromString to from-string )

instance
  From-string-String : From-string String
  From-string-String .From-string.Constraint _ = ⊤
  From-string-String .from-string s = s
