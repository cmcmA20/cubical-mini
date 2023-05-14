{-# OPTIONS --safe #-}
module Foundations.Equality where

open import Agda.Builtin.Equality public
  using ()
  renaming ( _≡_  to _＝ⁱ_
           ; refl to reflⁱ )
