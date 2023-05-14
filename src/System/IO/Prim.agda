{-# OPTIONS --safe #-}
module System.IO.Prim where

open import Agda.Builtin.IO public

open import Agda.Builtin.Coinduction
  using ()
  renaming ( ∞  to Delay
           ; ♯_ to later
           ; ♭  to force )
