{-# OPTIONS --safe #-}
module Foundations.Prim.Equiv where

open import Foundations.Prim.Type
open import Foundations.Sigma.Base

open import Agda.Builtin.Cubical.Equiv public
  using (_≃_; equiv-proof)
  renaming ( isEquiv       to is-equiv
           ; equivFun      to equiv-forward
           ; equivProof    to equiv-proof-fast
           ; pathToisEquiv to path→is-equiv-builtin
           ; pathToEquiv   to path→equiv-builtin
           )

private variable ℓ ℓ′ : Level

equiv-backward : {A : Type ℓ} {B : Type ℓ′} → A ≃ B → B → A
equiv-backward e y = e .snd .equiv-proof y .fst .fst