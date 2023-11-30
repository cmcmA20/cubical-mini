{-# OPTIONS --safe #-}
module Data.Fin.Interface where

open import Foundations.Base

open import Data.Empty.Base using (¬_)
open import Data.Nat.Base using (ℕ; zero; suc)

private variable
  ℓ ℓ′ : Level
  m : ℕ

record FinI {ℓ} (F : @0 ℕ → Type ℓ) : Typeω where
  no-eta-equality
  field
    fzero : ∀ᴱ[ n ꞉ ℕ ] F (suc n)
    fsuc  : ∀ᴱ[ n ꞉ ℕ ] (F n → F (suc n))
    elim  : Π[ P ꞉ ∀ᴱ[ n ꞉ ℕ ] (F n → Type ℓ′) ]
            Π[ fz ꞉ ∀ᴱ[ n ꞉ ℕ ] P {suc n} fzero ]
            Π[ fs ꞉ ∀ᴱ[ n ꞉ ℕ ] ∀[ k ꞉ F n ] (P k → P (fsuc k)) ]
            ∀[ n ꞉ ℕ ] Π[ k ꞉ F n ] P k
    ¬fin-0 : ¬ F 0
    fpred : ∀[ n ꞉ ℕ ] (F (suc (suc n)) → F (suc n))

  rec : ∀[ A ꞉ Type ℓ′ ]
        Π[ fz ꞉ A ]
        Π[ fs ꞉ ∀ᴱ[ n ꞉ ℕ ] (F n → A → A) ]
        ∀[ n ꞉ ℕ ] (F n → A)
  rec fz fs = elim _ fz (λ {_} {l} → fs l)
