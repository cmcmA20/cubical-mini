{-# OPTIONS --safe #-}
module Data.Reflection.Fixity where

open import Data.Bool.Base
open import Data.Float.Base

open import Agda.Builtin.Reflection
  public
  using ( left-assoc ; right-assoc; non-assoc
        ; Precedence ; related ; unrelated
        ; Fixity ; fixity
        )
  renaming ( Associativity to Associativity′ )

suc-precedence : Precedence → Precedence
suc-precedence (related x) = related (float-plus x (ℕ→float 1))
suc-precedence unrelated   = unrelated

prec-parens : Precedence → Precedence → Bool
prec-parens (related x) (related y) = y <ᵇ x
prec-parens unrelated   (related _) = true
prec-parens (related _) unrelated   = false
prec-parens unrelated   unrelated   = true

fixity→associativity : Fixity → Associativity′
fixity→associativity (fixity a _) = a

fixity→precedence : Fixity → Precedence
fixity→precedence (fixity _ p) = p
