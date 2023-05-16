{-# OPTIONS --safe #-}
module Structures.Path where

open import Foundations.Base
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ : Level
  S : Type ℓ → Type ℓ′

_on-paths-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

-- TODO need cong equiv
-- Path-str : Structure ℓ′ S → Structure _ (λ X → S on-paths-of X)
-- Path-str σ .is-hom (A , f) (B , g) h = let open Equiv h in
--   Π[ a ꞉ A ] Π[ a′ ꞉ A ] σ .is-hom
--     ((a ＝ a′) , f a a′)
--     ((to a ＝ to a′) , g (to a) (to a′))
--     {!!}

-- TODO
-- Path-str-is-univalent : {σ : Structure ℓ′ S} → is-univalent σ → is-univalent (Path-str σ)
-- Path-str-is-univalent is-univ f = {!!}
