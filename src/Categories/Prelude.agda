{-# OPTIONS --safe #-}
module Categories.Prelude where

open import Prelude
  renaming ( _≅_  to _≅ₜ_
           ; _↪_  to _↪ₜ_
           ; _×_  to _×ₜ_
           ; _∘_  to _∘ₜ_
           ; Iso  to Isoₜ
           ; id   to idₜ
           ; ≅→≃  to ≅ₜ→≃
           ; ≅→＝ to ≅ₜ→＝

           ; Extensional-↪ to Extensional-↪ₜ
           )
  public

open import Categories.Base public
open import Categories.Solver
  hiding ( module NbE ; module Reflection )
  public
open import Categories.Univalent
  using ( is-category ; path→iso ; Hom-pathᴾ
        ; Hom-transport ; Hom-pathᴾ-refl-l ; Hom-pathᴾ-refl-r
        ; module Univalent )
  public

open import Categories.Morphism.Instances public
