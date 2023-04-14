{-# OPTIONS --safe #-}
module Prim.Equiv where

open import Prim.Type
open import Prim.Data.Sigma

open import Agda.Builtin.Cubical.Equiv public
  using ()
  renaming ( isEquiv       to is-equiv′
           ; equiv-proof   to equiv-proof′
           ; _≃_           to _≃′_
           ; equivFun      to equiv-forward′
           ; equivProof    to equiv-proof′-fast
           ; pathToisEquiv to path-to-is-equiv′
           ; pathToEquiv   to path-to-equiv′
           )

private variable ℓ ℓ′ : Level

equiv-backward′ : {A : Type ℓ} {B : Type ℓ′} → A ≃′ B → B → A
equiv-backward′ e y = e .snd .equiv-proof′ y .fst .fst
