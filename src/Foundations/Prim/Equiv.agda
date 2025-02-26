{-# OPTIONS --safe #-}
module Foundations.Prim.Equiv where

open import Agda.Builtin.Cubical.Equiv public
  using ()
  renaming ( _≃_           to infix 1 _≃ᵇ_
           ; equiv-proof   to equiv-proofᵇ
           ; isEquiv       to is-equivᵇ
           ; equivFun      to equiv-forwardᵇ
           ; equivProof    to equiv-proof-fastᵇ
           ; pathToisEquiv to path→is-equivᵇ
           ; pathToEquiv   to path→equivᵇ
           )
