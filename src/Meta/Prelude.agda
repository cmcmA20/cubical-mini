{-# OPTIONS --safe #-}
module Meta.Prelude where

-- `ₜ` for typal
open import Foundations.Prelude
  renaming ( _$_  to _$ₜ_
           ; _$²_ to _$ₜ²_
           ; _$³_ to _$ₜ³_
           ; _$⁴_ to _$ₜ⁴_
           ; _$⁵_ to _$ₜ⁵_
           )
  hiding ( Σ-syntax
         ; Π-syntax
         ; ∀-syntax

         ; case_of_
         ; case_return_of_
         )
  public

open import Meta.Brackets  public
open import Meta.Inductive public
open import Meta.Variadic  public
