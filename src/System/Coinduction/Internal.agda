{-# OPTIONS --safe --guardedness #-}
module System.Coinduction.Internal where

open import Agda.Builtin.Coinduction
  using ()
  renaming ( ∞  to Delay
           ; ♯_ to later
           ; ♭  to force )
