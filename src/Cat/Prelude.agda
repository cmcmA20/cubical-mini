{-# OPTIONS --safe #-}
module Cat.Prelude where

open import Prelude
  renaming ( _↪_ to _↪ₜ_
           ; _↠_ to _↠ₜ_
           ; _∘_ to _∘ₜ_
           ; id  to idₜ
           ; ≅→≃ to ≅ₜ→≃
           ; ≅→= to ≅ₜ→=
           ; ×-assoc to ×ₜ-assoc

           ; Extensional-↪ to Extensional-↪ₜ
           ; Extensional-↠ to Extensional-↠ₜ
           )
  public

open import Structures.n-Type public

open import Cat.Base public
open import Cat.Functor.Base public
open import Cat.NT public
open import Cat.Solver
  hiding ( module NbE ; module Reflection )
  public
open import Cat.Univalent
  using ( is-category ; path→equiv ; Hom-pathᴾ
        ; Hom-transport ; Hom-pathᴾ-refl-l ; Hom-pathᴾ-refl-r
        ; module Univalent )
  public

open import Cat.Morphism.Instances public

open import Functions.Equiv.Biinv public
