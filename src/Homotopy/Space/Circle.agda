{-# OPTIONS --safe #-}
module Homotopy.Space.Circle where

open import Foundations.Base

data S¹ : 𝒰 where
  base : S¹
  loop : base ＝ base

elim : {ℓ : Level} {P : S¹ → 𝒰 ℓ}
       (pb : P base)
     → ＜ pb ／ (λ i → P (loop i)) ＼ pb ＞
     → Π[ s ꞉ S¹ ] P s
elim pb _ base     = pb
elim _  q (loop i) = q i

rec : {ℓ : Level} {A : 𝒰 ℓ}
    → Π[ a ꞉ A ] (a ＝ a → S¹ → A)
rec = elim
