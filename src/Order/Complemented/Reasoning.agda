{-# OPTIONS --safe #-}
open import Cat.Prelude
open import Order.Base
open import Order.Complemented
open import Order.Strict
open import Order.Total
open import Order.Trichotomous

module Order.Complemented.Reasoning {o ℓ} (C : ComplementedPoset o ℓ) where
  open ComplementedPoset
  open Poset (complemented→poset C)
    hiding ( Ob )
    public
  open StrictPoset (complemented→strict C)
    hiding ( Ob )
    public
  open ComplementedPoset C
    using ( Ob ; ≤≃≯ ; <≃≱ ; ≤→≯ ; ≯→≤ ; <→≱ ; ≱→< ; <→≤ ; ≤→<⊎= ; <⊎=→≤ ; ≤≃<⊎=)
    public
  open is-weak-total-order (has-weak-total-order C)
    using ( from-≰ )
    public
  open is-decidable-total-order (has-dec-total-order C)
    using ( compare ; _≤?_ ; _≥?_ ; _≰?_ ; _≱?_ )
    public
  open is-decidable-strict-total-order (has-dec-strict-total-order C)
    using ( <-weak-linear ; <-connex ; _<?_ ; _>?_ ; _≮?_ ; _≯?_ )
    public
  open is-trichotomous (has-tri-order C)
    using ( trisect ; ⌊_⌋≟ ; ⌊_⌋<¿ ; ⌊_⌋>¿ )
    public
