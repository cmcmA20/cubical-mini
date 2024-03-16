{-# OPTIONS --safe #-}
module Meta.Prelude where

-- `ₜ` for typal
open import Foundations.Prelude
  renaming ( _$_  to _$ₜ_
           ; _$²_ to _$ₜ²_
           ; _$³_ to _$ₜ³_
           ; _$⁴_ to _$ₜ⁴_
           ; _$⁵_ to _$ₜ⁵_
           ; _&_  to _&ₜ_
           ; _∘_  to _∘ₜ_
           ; _∘′_ to _∘ₜ′_
           ; id   to idₜ

           ; _∙_  to _∙ₚ_
           ; sym  to symₚ
           ; refl to reflₚ

           ; J       to Jₜ
           ; J-refl  to Jₜ-refl
           ; J-∙     to Jₜ-∙
           ; J-dep   to Jₜ-dep
           ; J²      to Jₜ²
           ; J²-refl to Jₜ²-refl
           ; J>_     to Jₜ>_
           )
  hiding ( Σ-syntax
         ; Π-syntax
         ; ∀-syntax )
  public

open import Meta.Groupoid public
open import Meta.Variadic public
