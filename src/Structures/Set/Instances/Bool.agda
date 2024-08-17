{-# OPTIONS --safe #-}
module Structures.Set.Instances.Bool where

open import Meta.Prelude

open import Structures.Set.Base

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects

module _ {ℓ} {A : 𝒰 ℓ} ⦃ _ : is-discrete A ⦄ where

  private module X where
    S = A → Bool

    variable
      s : S
      x y : A

    ∅ : S
    ∅ _ = false

    lookup : S → A → Bool
    lookup = id

    insert : S → A → S
    insert s x a with x ≟ a
    ... | yes _ = true
    ... | no  _ = s a

    remove : S → A → S
    remove s x a with x ≟ a
    ... | yes _ = false
    ... | no  _ = s a

    lookup-empty : Erased (lookup ∅ x ＝ false)
    lookup-empty .erased = refl

    lookup-insert : Erased (lookup (insert s x) x ＝ true)
    lookup-insert {x} .erased with x ≟ x
    ... | yes _   = refl
    ... | no  x≠x = false! x≠x

    lookup-remove : Erased (lookup (remove s x) x ＝ false)
    lookup-remove {x} .erased with x ≟ x
    ... | yes _   = refl
    ... | no  x≠x = false! x≠x

    insert-nop    : lookup s x ＝ true
                  → Erased (insert s x ＝ s)
    insert-nop {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (p ⁻¹ ∙ ap s x=a) i
    ... | no  _   = s a

    insert-insert : Erased (insert (insert s x) y ＝ insert (insert s y) x)
    insert-insert {s} {x} {y} .erased i a with x ≟ a
    insert-insert {s} {x} {y} .erased i a | yes x=a with y ≟ a
    ... | yes _   = true
    ... | no  y≠a with x ≟ a
    ... | yes _   = true
    ... | no  x≠a = false! {Q = s a ＝ true} (x≠a x=a) i
    insert-insert {s} {x} {y} .erased i a | no  x≠a with y ≟ a
    ... | yes _ = true
    ... | no  y≠a with x ≟ a
    ... | yes x=a = false! {Q = true ＝ s a} (x≠a x=a) i
    ... | no  _ = s a


    insert-remove : lookup s x ＝ true
                  → Erased (insert (remove s x) x ＝ s)
    insert-remove {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (p ⁻¹ ∙ ap s x=a ) i
    ... | no  x≠a with x ≟ a
    ... | yes x=a = false! {Q = false ＝ s a} (x≠a x=a) i
    ... | no  x≠a = s a

    remove-nop    : lookup s x ＝ false
                  → Erased (remove s x ＝ s)
    remove-nop {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (p ⁻¹ ∙ ap s x=a) i
    ... | no  x≠a = s a

    remove-remove : Erased (remove (remove s x) y ＝ remove (remove s y) x)
    remove-remove {s} {x} {y} .erased i a with x ≟ a
    remove-remove {s} {x} {y} .erased i a | yes x=a with y ≟ a
    ... | yes _ = false
    ... | no  y≠a with x ≟ a
    ... | yes _ = false
    ... | no  x≠a = false! {Q = s a ＝ false} (x≠a x=a) i
    remove-remove {s} {x} {y} .erased i a | no x≠a with y ≟ a
    ... | yes _ = false
    ... | no  y≠a with x ≟ a
    ... | yes x=a = false! {Q = false ＝ s a} (x≠a x=a) i
    ... | no  _ = s a

    remove-insert : lookup s x ＝ false
                  → Erased (remove (insert s x) x ＝ s)
    remove-insert {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (p ⁻¹ ∙ ap s x=a ) i
    ... | no  x≠a with x ≟ a
    ... | yes x=a = false! {Q = true ＝ s a} (x≠a x=a) i
    ... | no  _ = s a

  impl : SetI A (A → Bool)
  impl = record {X ; lookup-empty = λ {x} → X.lookup-empty {x} }
