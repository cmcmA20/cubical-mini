{-# OPTIONS --safe --guardedness #-}
module Prim.Coinduction where

open import Agda.Builtin.Coinduction
  using ()
  renaming ( ∞  to Delay
           ; ♯_ to later
           ; ♭  to force )
