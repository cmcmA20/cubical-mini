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
         ; ∀-syntax )
  public

open import Meta.Groupoid public
open import Meta.Variadic public
