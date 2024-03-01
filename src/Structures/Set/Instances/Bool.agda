{-# OPTIONS --safe #-}
module Structures.Set.Instances.Bool where

open import Foundations.Base

open import Meta.Search.Discrete

open import Structures.Set.Base

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base as ⊥

module _ {ℓ} {A : 𝒰 ℓ} ⦃ _ : is-discrete A ⦄ where

  private module X where
    S = A → Bool

    variable
      s : S
      x y : A

    empty : S
    empty _ = false

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

    lookup-empty : Erased $ᴱ lookup empty x ＝ false
    lookup-empty .erased = refl

    lookup-insert : Erased $ᴱ lookup (insert s x) x ＝ true
    lookup-insert {x} .erased with x ≟ x
    ... | yes _   = refl
    ... | no  x≠x = ⊥.rec (x≠x refl)

    lookup-remove : Erased $ᴱ lookup (remove s x) x ＝ false
    lookup-remove {x} .erased with x ≟ x
    ... | yes _   = refl
    ... | no  x≠x = ⊥.rec (x≠x refl)

    insert-nop    : lookup s x ＝ true
                  → Erased $ᴱ insert s x ＝ s
    insert-nop {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (sym p ∙ ap s x=a) i
    ... | no  _   = s a

    insert-insert : Erased $ᴱ insert (insert s x) y ＝ insert (insert s y) x
    insert-insert {s} {x} {y} .erased i a with x ≟ a
    insert-insert {s} {x} {y} .erased i a | yes x=a with y ≟ a
    ... | yes _   = true
    ... | no  y≠a with x ≟ a
    ... | yes _   = true
    ... | no  x≠a = ⊥.rec {A = s a ＝ true} (x≠a x=a) i
    insert-insert {s} {x} {y} .erased i a | no  x≠a with y ≟ a
    ... | yes _ = true
    ... | no  y≠a with x ≟ a
    ... | yes x=a = ⊥.rec {A = true ＝ s a} (x≠a x=a) i
    ... | no  _ = s a


    insert-remove : lookup s x ＝ true
                  → Erased $ᴱ insert (remove s x) x ＝ s
    insert-remove {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (sym p ∙ ap s x=a ) i
    ... | no  x≠a with x ≟ a
    ... | yes x=a = ⊥.rec {A = false ＝ s a} (x≠a x=a) i
    ... | no  x≠a = s a

    remove-nop    : lookup s x ＝ false
                  → Erased $ᴱ remove s x ＝ s
    remove-nop {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (sym p ∙ ap s x=a) i
    ... | no  x≠a = s a

    remove-remove : Erased $ᴱ remove (remove s x) y ＝ remove (remove s y) x
    remove-remove {s} {x} {y} .erased i a with x ≟ a
    remove-remove {s} {x} {y} .erased i a | yes x=a with y ≟ a
    ... | yes _ = false
    ... | no  y≠a with x ≟ a
    ... | yes _ = false
    ... | no  x≠a = ⊥.rec {A = s a ＝ false} (x≠a x=a) i
    remove-remove {s} {x} {y} .erased i a | no x≠a with y ≟ a
    ... | yes _ = false
    ... | no  y≠a with x ≟ a
    ... | yes x=a = ⊥.rec {A = false ＝ s a} (x≠a x=a) i
    ... | no  _ = s a

    remove-insert : lookup s x ＝ false
                  → Erased $ᴱ remove (insert s x) x ＝ s
    remove-insert {s} {x} p .erased i a with x ≟ a
    ... | yes x=a = (sym p ∙ ap s x=a ) i
    ... | no  x≠a with x ≟ a
    ... | yes x=a = ⊥.rec {A = true ＝ s a} (x≠a x=a) i
    ... | no  _ = s a

  impl : SetI A (A → Bool)
  impl = record {X ; lookup-empty = λ {x} → X.lookup-empty {x} }
