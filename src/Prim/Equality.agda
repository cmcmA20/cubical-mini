{-# OPTIONS --safe #-}
module Prim.Equality where

open import Agda.Builtin.Equality public
  using ()
  renaming ( _≡_  to _＝ⁱ_
           ; refl to reflⁱ )
