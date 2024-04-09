{-# OPTIONS --safe #-}
module Functions.Equiv.Weak where

open import Meta.Prelude

-- Weak equivalences are actually builtin in Agda
open import Foundations.Equiv public

open import Meta.Effect.Bind
open import Meta.Extensionality

open import Data.Truncation.Propositional

open import Functions.Embedding
open import Functions.Surjection

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B

is-surjective-embedding→is-equiv : is-surjective f → is-embedding f → is-equiv f
is-surjective-embedding→is-equiv sur emb .equiv-proof y = proj!
  ⦇ inhabited-prop-is-contr (sur y) ⦇ (emb y) ⦈ ⦈

is-surjective-embedding≃is-equiv : is-surjective f × is-embedding f ≃ is-equiv f
is-surjective-embedding≃is-equiv = prop-extₑ!
  (is-surjective-embedding→is-equiv $ₜ²_)
  < is-equiv→is-surjective , is-equiv→is-embedding >

≃→extensional
  : B ≃ A
  → Extensional A ℓ″
  → Extensional B ℓ″
≃→extensional f = ↪→extensional (≃→↪ f)

-- TODO move?
≅→extensional
  : Iso B A
  → Extensional A ℓ″
  → Extensional B ℓ″
≅→extensional f = ≃→extensional (≅→≃ f)

instance
  Extensional-≃
    : {A : Type ℓ} ⦃ sb : Extensional (A → B) ℓ″ ⦄
    → Extensional (A ≃ B) ℓ″
  Extensional-≃ ⦃ sb ⦄ = Σ-prop→extensional! sb
