{-# OPTIONS --safe #-}
module Functions.Equiv.Weak where

open import Foundations.Base
-- Weak equivalences are actually builtin in Agda
open import Foundations.Equiv public
open import Foundations.Sigma

open import Meta.Effect.Bind
open import Meta.Search.HLevel

open import Functions.Embedding
open import Functions.Surjection

open import Truncation.Propositional

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B

is-surjective-embedding→is-equiv : is-surjective f → is-embedding f → is-equiv f
is-surjective-embedding→is-equiv sur emb .equiv-proof y =
  is-contr-β $ proj! ⦇ inhabited-prop-is-contr (sur y) (pure (emb y)) ⦈

is-surjective-embedding≃is-equiv : is-surjective f × is-embedding f ≃ is-equiv f
is-surjective-embedding≃is-equiv = prop-extₑ!
  (is-surjective-embedding→is-equiv $²_)
  (λ fe → is-equiv→is-surjective fe , is-equiv→is-embedding fe)
