{-# OPTIONS --safe #-}
module Data.Fin.Computational.Base where

open import Foundations.Prelude

open import Data.Bool.Base
  using (is-true)
import Data.Empty.Base as ⊥
open import Data.Fin.Interface
open import Data.Nat.Base
  using (ℕ; zero; suc ; pred)
open import Data.Nat.Order.Inductive.Base
open import Data.Sum.Base

private variable
  ℓ ℓ′ : Level
  @0 m n : ℕ

record Fin (@0 n : ℕ) : Type where
  constructor mk-fin
  field
    index     : ℕ
    { bound } : Erased (is-true (index <? n))

open Fin

fzero : Fin (suc n)
fzero = mk-fin 0

fsuc : Fin n → Fin (suc n)
fsuc (mk-fin k {(b)}) = mk-fin (suc k) {b}

fsplit
  : (k : Fin (suc n))
  → (k ＝ fzero) ⊎ (Σ[ l ꞉ Fin n ] (k ＝ fsuc l))
fsplit (mk-fin 0)       = inl refl
fsplit (mk-fin (suc k)) = inr (mk-fin k , refl)

-- TODO mmm noice
-- elim  : Π[ P ꞉ ∀ᴱ[ n ꞉ ℕ ] (Fin n → Type ℓ′) ]
--         Π[ fz ꞉ ∀ᴱ[ n ꞉ ℕ ] P {suc n} fzero ]
--         Π[ fs ꞉ ∀ᴱ[ n ꞉ ℕ ] ∀[ k ꞉ Fin n ] (P k → P (fsuc k)) ]
--         ∀ᴱ[ n ꞉ ℕ ] Π[ k ꞉ Fin n ] P k
-- elim P fz fs {x = n} (mk-fin 0 {∣ b ∣ᴱ}) =
--   let @0 p : _
--       p = <→s {n = n} b
--       @0 n′ : ℕ
--       n′ = p .fst
--       @0 q : n ＝ suc n′
--       q = p .snd
--   in substᴱ {A = Σ[ m ꞉ ℕ ] Fin m × ∥ 0 < m ∥ᴱ}
--             {x = suc n′ , fzero , ∣ z≤ {n′} ∣ᴱ}
--             {y = n , (substᴱ Fin (sym q) fzero) , ∣ b ∣ᴱ}
--             (λ x → P {x .fst} (mk-fin 0 {∣ erased (x .snd .snd) ∣ᴱ}))
--             (Σ-path (sym q) $ ×-path refl (is-prop-β (∥-∥ᴱ-is-prop (<-is-prop {0} {n})) _ _)) fz
-- elim P fz fs {x = n} (mk-fin (suc k) {∣ b ∣ᴱ}) = {!!}

elim  : Π[ P ꞉ ∀ᴱ[ n ꞉ ℕ ] (Fin n → Type ℓ′) ]
        Π[ fz ꞉ ∀ᴱ[ n ꞉ ℕ ] P {suc n} fzero ]
        Π[ fs ꞉ ∀ᴱ[ n ꞉ ℕ ] ∀[ k ꞉ Fin n ] (P k → P (fsuc k)) ]
        ∀[ n ꞉ ℕ ] Π[ k ꞉ Fin n ] P k
elim P fz fs {x = suc n} (mk-fin 0) = fz
elim P fz fs {x = suc n} (mk-fin (suc k)) = fs (elim P fz fs (mk-fin k))

-- TODO wait for the right eliminator
-- impl : FinIᴱ Fin
-- impl .FinIᴱ.fzero = fzero
-- impl .FinIᴱ.fsuc = fsuc
-- impl .FinIᴱ.fsplit = fsplit
-- impl .FinIᴱ.elim = elim

fin→ℕ : Fin n → ℕ
fin→ℕ (mk-fin k) = k

module _ where
  open import Data.Fin.Base
    renaming (Fin to Finᵈ; fzero to fzeroᵈ; fsuc to fsucᵈ)

  default≃computational : ∀{n} → Finᵈ n ≃ Fin n
  default≃computational = ≅→≃ $ to , iso from ri li where
    to : ∀{n} → Finᵈ n → Fin n
    to {suc _} fzeroᵈ    = fzero
    to {suc _} (fsucᵈ k) = fsuc (to k)

    from : ∀{n} → Fin n → Finᵈ n
    from {suc _} (mk-fin 0)                   = fzeroᵈ
    from {suc _} (mk-fin (suc k) {bound = b}) = fsucᵈ (from (mk-fin k {b}))

    ri : ∀{n} k → to {n} (from k) ＝ k
    ri {suc _} (mk-fin 0)       = refl
    ri {suc _} (mk-fin (suc k)) = ap fsuc (ri (mk-fin k))

    li : ∀{n} k → from {n} (to k) ＝ k
    li {suc _} fzeroᵈ    = refl
    li {suc _} (fsucᵈ k) = ap fsucᵈ (li k)

  module default≃computational {n} = Equiv (default≃computational {n})
