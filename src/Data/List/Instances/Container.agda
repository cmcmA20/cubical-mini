{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Instances.Container where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Container

open import Data.Container
open import Data.List.Base
open import Data.Nat.Base
open import Data.Fin.Base as Fin

Listᶜ : Container _ _
Listᶜ = ℕ ▶ Fin

private variable
  ℓ : Level
  A : Type ℓ

cons : A → ⟦ Listᶜ ⟧ A → ⟦ Listᶜ ⟧ A
cons a (n , _) .fst = suc n
cons a (_ , f) .snd fzero    = a
cons a (_ , f) .snd (fsuc k) = f k

list→cont : List A → ⟦ Listᶜ ⟧ A
list→cont []       = 0 , λ ()
list→cont (x ∷ xs) = cons x (list→cont xs)

cont→list : (n : ℕ) (f : Fin n → A) → List A
cont→list 0       _ = []
cont→list (suc n) f = f fzero ∷ cont→list n (f ∘ fsuc)

private
  l→c→l : (xs : List A) → cont→list $² (list→cont xs) ＝ xs
  l→c→l []       = refl
  l→c→l (x ∷ xs) = ap (x ∷_) (l→c→l xs)

  c→l→c : (n : ℕ) (f : Fin n → A) → list→cont (cont→list n f) ＝ (n , f)
  c→l→c 0       _ = refl ,ₚ fun-ext λ()
  c→l→c (suc n) f = Σ-path (ap (suc ∘ fst) ih) $ fun-ext go
    where
    ih = c→l→c n (f ∘ fsuc)
    go : (k : Fin _) → _
    go fzero    = transport-refl _
    go (fsuc k) = from-pathᴾ (snd # ih) # k

list≃cont : List A ≃ ⟦ Listᶜ ⟧ A
list≃cont = ≅→≃ $ iso list→cont (cont→list $²_)
  (fun-ext $ c→l→c $²_) (fun-ext l→c→l)

instance
  AC-List : Abstract-Container (eff List)
  AC-List = make-abstract-container Listᶜ list≃cont
