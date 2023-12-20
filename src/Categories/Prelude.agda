{-# OPTIONS --safe #-}
module Categories.Prelude where

open import Prelude
  renaming ( _∘_       to _∘ₜ_
           ; id        to idₜ
           ; _≅_       to _≅ₜ_
           ; _↪_       to _↪ₜ_
           ; _×_       to _×ₜ_
           ; iso→path  to isoₜ→path
           ; iso→equiv to isoₜ→equiv
           )
  -- FIXME remove after fixing search tactic
  hiding ( Tactic-bishop-finite
         ; Tactic-discrete
         ; Tactic-manifest-bishop-finite)
  public

open import Categories.Base public
open import Categories.Solver
  hiding ( module NbE ; module Reflection )
  public
open import Categories.Univalent
  using ( is-category ; path→iso ; Hom-pathP
        ; Hom-transport ; Hom-pathP-refl-l ; Hom-pathP-refl-r
        ; module Univalent )
  public

open import Categories.Morphism.Extensionality public
