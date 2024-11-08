{-# OPTIONS --safe --no-exact-split #-}
module Data.Vec.Inductive.Instances.Container where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Container

open import Data.Container
open import Data.Fin.Base as Fin
open import Data.Nat.Base
open import Data.Unit.Base
open import Data.Vec.Inductive.Base

Vecᶜ : ℕ → Container _ _
Vecᶜ n = ⊤ ▶ λ _ → Fin n

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

cons : A → ⟦ Vecᶜ n ⟧ A → ⟦ Vecᶜ (suc n) ⟧ A
cons x (_ , _) .fst = _
cons x (_ , _) .snd fzero = x
cons x (_ , f) .snd (fsuc k) = f k

vec→cont : Vec A n → ⟦ Vecᶜ n ⟧ A
vec→cont {n = 0}     []       = _ , λ()
vec→cont {n = suc n} (x ∷ xs) = cons x (vec→cont xs)

cont→vec : (f : Fin n → A) → Vec A n
cont→vec {n = 0}     _ = []
cont→vec {n = suc n} f = f fzero ∷ cont→vec (f ∘ fsuc)

private opaque
  v→c→v : (xs : Vec A n) → cont→vec (vec→cont xs .snd) ＝ xs
  v→c→v {n = 0}     []       = refl
  v→c→v {n = suc n} (x ∷ xs) = x ∷_ $ v→c→v xs

  c→v→c : (f : Fin n → A) (k : Fin n) → vec→cont (cont→vec f) .snd k ＝ f k
  c→v→c {n = suc n} f fzero    = refl
  c→v→c {n = suc n} f (fsuc k) = c→v→c (f ∘ fsuc) k

vec≃cont : Vec A n ≃ ⟦ Vecᶜ n ⟧ A
vec≃cont = ≅→≃ $ iso vec→cont (cont→vec ∘ snd)
  (fun-ext λ x → refl ,ₚ fun-ext (c→v→c (x .snd)))
  (fun-ext v→c→v)

instance
  AC-Vec : Abstract-Container (eff (λ T → Vec T n))
  AC-Vec {n} = make-abstract-container (Vecᶜ n) vec≃cont
