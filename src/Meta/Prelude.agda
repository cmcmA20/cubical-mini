{-# OPTIONS --safe #-}
module Meta.Prelude where

-- `ₜ` for typal
open import Foundations.Prelude
  renaming ( _$_  to _$ₜ_
           ; _$²_ to _$ₜ²_
           ; _$³_ to _$ₜ³_
           ; _$⁴_ to _$ₜ⁴_
           ; _$⁵_ to _$ₜ⁵_
           ; _∘ˢ_ to _∘ₜˢ_

           ; _∙_  to _∙ₚ_
           ; sym  to symₚ
           ; refl to reflₚ
           )
  hiding ( Σ-syntax
         ; Π-syntax
         ; ∀-syntax

         ; case_of_
         ; case_return_of_
         )
  public

open import Meta.Brackets  public
open import Meta.Groupoid  public
open import Meta.Inductive public
open import Meta.Variadic  public

open import Structures.n-Type public
