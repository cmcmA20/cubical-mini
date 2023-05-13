{-# OPTIONS --safe #-}
module Foundations.Equiv.Internal where

open import Foundations.Type.Internal
open import Foundations.Sigma.Internal

open import Agda.Builtin.Cubical.Equiv public
  using (_≃_)
  renaming ( isEquiv       to is-equiv
           ; equiv-proof   to equiv-proof
           ; equivFun      to equiv-forward
           ; equivProof    to equiv-proof-fast
           ; pathToisEquiv to path-to-is-equiv
           ; pathToEquiv   to path-to-equiv
           )

private variable ℓ ℓ′ : Level

equiv-backward : {A : Type ℓ} {B : Type ℓ′} → A ≃ B → B → A
equiv-backward e y = e .snd .equiv-proof y .fst .fst
