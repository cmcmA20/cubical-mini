{-# OPTIONS --safe #-}
module Meta.Deriving.HLevel where

open import Meta.Prelude

open import Meta.Record
open import Meta.Reflection.Base
open import Meta.Reflection.Signature

open import Structures.n-Type

open import Data.Nat.Order.Inductive
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Map

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

private
  record-hlevel-instance
    : {A : Type ℓ} {B : Type ℓ′} (n : ℕ) ⦃ A-hl : H-Level n A ⦄
    → Iso B A
    → ∀ {k} ⦃ p : n ≤ k ⦄
    → H-Level k B
  record-hlevel-instance n im ⦃ p ⦄ = hlevel-instance $
    ≅→is-of-hlevel _ im (is-of-hlevel-≤ _ _ p (hlevel _))

declare-record-hlevel : (n : ℕ) → Name → Name → TC ⊤
declare-record-hlevel n inst rec = do
  (rec-tele , _) ← pi-view <$> get-type rec

  eqv ← helper-function-name rec "isom"
  declare-record-iso eqv rec

  let
    args    = reverse-fast $ map-up (λ n → snd ∘ second (map λ _ → var₀ n)) 2
      (reverse-fast rec-tele)
    head-ty = it H-Level ##ₙ var₀ 1 ##ₙ def rec args
    inst-ty = unpi-view (map (second (argH ∘ unarg)) rec-tele) $
      pi (argH (it ℕ)) $ abs "n" $
      pi (argI (it _≤_ ##ₙ lit (nat n) ##ₙ var₀ 0)) $ abs "le" $
      head-ty

  declare-def (argI inst) inst-ty
  define-function inst
    [ clause [] [] (it record-hlevel-instance ##ₙ lit (nat n) ##ₙ def₀ eqv) ]


-- Usage
module _ where private
  open import Data.Nat.Path

  record T : Type where
    no-eta-equality
    field
      x y  : ℕ
      two : Erased (x ＝ y)
      three : x < y

  unquoteDecl kek = declare-record-hlevel 2 kek (quote T)

  ror : {n : ℕ} ⦃ le : 2 ≤ n ⦄ → H-Level n T
  ror = kek
