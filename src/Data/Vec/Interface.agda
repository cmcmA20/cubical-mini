{-# OPTIONS --safe #-}
module Data.Vec.Interface where

open import Foundations.Base

open import Data.Nat.Base
  using (ℕ; zero; suc)

private variable
  ℓ ℓ′ : Level

record VecI (V : ∀{ℓ} → Type ℓ → ℕ → Type ℓ) : Typeω where
  no-eta-equality
  field
    []   : ∀[ A ꞉ Type ℓ ] V A 0
    _∷_  : ∀[ A ꞉ Type ℓ ] ∀[ n ꞉ ℕ ] (A → V A n → V A (suc n))
    elim : ∀{ℓ ℓ′ : Level}
         → ∀[ A ꞉ Type ℓ ]
           Π[ P ꞉ ∀[ n ꞉ ℕ ] (V A n → Type ℓ′) ]
           Π[ p[] ꞉ P [] ]
           Π[ p∷ ꞉ ∀[ n ꞉ ℕ ] ∀[ x ꞉ A ] ∀[ xs ꞉ V A n ] (P xs → P (x ∷ xs)) ]
           ∀[ n ꞉ ℕ ] Π[ xs ꞉ V A n ] P xs

  rec : ∀{ℓ ℓ′ : Level}
      → ∀[ A ꞉ Type ℓ ]
        ∀[ P ꞉ (ℕ → Type ℓ′) ]
        Π[ pz ꞉ P 0 ]
        Π[ ps ꞉ ∀[ n ꞉ ℕ ] Π[ x ꞉ A ] (P n → P (suc n)) ]
        ∀[ n ꞉ ℕ ] Π[ xs ꞉ V A n ] P n
  rec {_} {_} {_} {x = P} pz ps = elim (λ {n} _ → P n) pz (λ {_} {x} → ps x)


record VecIᴱ (V : ∀{ℓ} → Type ℓ → @0 ℕ → Type ℓ) : Typeω where
  no-eta-equality
  field
    []   : ∀[ A ꞉ Type ℓ ] V A 0
    _∷_  : ∀[ A ꞉ Type ℓ ] ∀ᴱ[ n ꞉ ℕ ] (A → V A n → V A (suc n))
    elim : ∀{ℓ ℓ′ : Level}
         → ∀[ A ꞉ Type ℓ ]
           Π[ P ꞉ (∀ᴱ[ n ꞉ ℕ ] (V A n → Type ℓ′)) ]
           Π[ p[] ꞉ P [] ]
           Π[ p∷ ꞉ (∀ᴱ[ n ꞉ ℕ ] ∀[ x ꞉ A ] ∀[ xs ꞉ V A n ] (P xs → P (x ∷ xs))) ]
           ∀ᴱ[ n ꞉ ℕ ] Π[ xs ꞉ V A n ] P xs

  rec : ∀{ℓ ℓ′ : Level}
      → ∀[ A ꞉ Type ℓ ]
        ∀[ P ꞉ (@0 ℕ → Type ℓ′) ]
        Π[ pz ꞉ P 0 ]
        Π[ ps ꞉ ∀ᴱ[ n ꞉ ℕ ] Π[ x ꞉ A ] (P n → P (suc n)) ]
        ∀ᴱ[ n ꞉ ℕ ] Π[ xs ꞉ V A n ] P n
  rec {_} {_} {_} {x = P} pz ps = elim (λ {n} _ → P n) pz (λ {_} {x} → ps x)
