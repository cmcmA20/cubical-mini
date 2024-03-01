{-# OPTIONS --safe #-}
-- This is a programmer's set (like in OCaml), not a mathematician's one
module Structures.Set.Base where

open import Foundations.Base

open import Meta.Membership
open import Meta.Record

open import Data.Bool.Base

-- `A` is the type of elements, `S` is an implementation
module _ {ℓᵃ ℓ} (A : 𝒰 ℓᵃ) (S : 𝒰 ℓ) where
  private variable
    s : S
    x y : A

  record SetI : 𝒰 (ℓᵃ ⊔ ℓ) where
    no-eta-equality
    field
      empty  : S
      lookup : S → A → Bool
      insert remove : S → A → S

      lookup-empty  : Erased $ᴱ lookup empty x ＝ false
      lookup-insert : Erased $ᴱ lookup (insert s x) x ＝ true
      lookup-remove : Erased $ᴱ lookup (remove s x) x ＝ false
      insert-nop    : lookup s x ＝ true
                    → Erased $ᴱ insert s x ＝ s
      insert-insert : Erased $ᴱ insert (insert s x) y ＝ insert (insert s y) x
      insert-remove : lookup s x ＝ true
                    → Erased $ᴱ insert (remove s x) x ＝ s
      remove-nop    : lookup s x ＝ false
                    → Erased $ᴱ remove s x ＝ s
      remove-remove : Erased $ᴱ remove (remove s x) y ＝ remove (remove s y) x
      remove-insert : lookup s x ＝ false
                    → Erased $ᴱ remove (insert s x) x ＝ s

    instance
      Membership-set : Membership A S 0ℓ
      Membership-set ._∈_ a s = lookup s a ＝ true

unquoteDecl SetI-iso = declare-record-iso SetI-iso (quote SetI)
