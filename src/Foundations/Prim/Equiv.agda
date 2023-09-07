{-# OPTIONS --safe #-}
module Foundations.Prim.Equiv where

open import Foundations.Prim.Type
open import Foundations.Sigma.Base

open import Agda.Builtin.Cubical.Equiv public
  using (equiv-proof)
  renaming ( _≃_           to infix 1 _≃_
           ; isEquiv       to is-equiv
           ; equivFun      to equiv-forward
           ; equivProof    to builtin-equiv-proof-fast
           ; pathToisEquiv to builtin-path→is-equiv
           ; pathToEquiv   to builtin-path→equiv
           )

private variable ℓ ℓ′ : Level

equiv-backward : {A : Type ℓ} {B : Type ℓ′} → A ≃ B → B → A
equiv-backward e y = e .snd .equiv-proof y .fst .fst
