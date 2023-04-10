{-# OPTIONS --safe #-}
module Prim.Equiv where

open import Prim.Type
open import Prim.Data.Sigma

private variable ℓ ℓ′ : Level

open import Agda.Builtin.Cubical.Equiv public
  using ()
  renaming ( isEquiv       to isEquiv′
           ; equiv-proof   to equiv-proof′
           ; _≃_           to _≃′_
           ; equivFun      to forward′
           ; equivProof    to equivProof′
           ; pathToisEquiv to pathToisEquiv′
           ; pathToEquiv   to pathToEquiv′
           )

backward′ : {A : Type ℓ} {B : Type ℓ′} → A ≃′ B → B → A
backward′ e y = e .snd .equiv-proof′ y .fst .fst
