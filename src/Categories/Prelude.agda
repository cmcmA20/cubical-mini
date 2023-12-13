{-# OPTIONS --safe #-}
module Categories.Prelude where

open import Prelude
  renaming ( _∘_ to _∘ₜ_
           ; id  to idₜ
           ; _≅_ to _≅ₜ_
           ; _↪_ to _↪ₜ_
           )
  public

open import Categories.Base public
open import Categories.Solver
  hiding (module NbE; module Reflection)
  public

-- TODO other reexports
