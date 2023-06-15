{-# OPTIONS --safe #-}
module Meta.Literals.FromString where

open import Data.String.Base
open import Data.Unit.Base

open import Agda.Builtin.FromString public
  using ( IsString )
  renaming ( fromString to from-string )

instance
  IsString-String : IsString String
  IsString-String .IsString.Constraint _ = ⊤
  IsString-String .IsString.fromString s = s
