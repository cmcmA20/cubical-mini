{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Correspondences.Unary.Any where

open import Foundations.Base
  hiding (Σ-syntax; Π-syntax; ∀-syntax)

open import Meta.Effect.Idiom
open import Meta.Search.Discrete
open import Meta.Variadic

open import Correspondences.Decidable

open import Data.Dec as Dec
open import Data.Fin.Inductive.Base
open import Data.Fin.Inductive.Instances.Discrete
open import Data.Vec.Inductive.Instances.Idiom
open import Data.Vec.Inductive.Operations
open import Data.Sum.Base
open import Data.Sum.Instances.Decidable

private variable
  a a′ : Level
  A : Type a
  P : Pred A a′
  n : ℕ

Any : ∀ {a a′} {n} {A : Type a} (P : Pred A a′) → Vec A n → Type _
Any {n} P xs = Σ[ idx ꞉ Fin n ] P (lookup xs idx)

any? : Decidable P → Decidable (λ (xs : Vec A n) → Any P xs)
any? {n = 0}     P? [] = no λ()
any? {n = suc n} P? (x ∷ xs) =
  Dec.dmap [ (fzero ,_) , bimap fsuc id ]ᵤ
           (λ { ¬ps (fzero  , p ) → ¬ps (inl p)
              ; ¬ps (fsuc i , ps) → ¬ps (inr (_ , ps)) })
           (⊎-decision (P? x) (any? P? xs))

any-ap
  : {a a′ b b′ : Level} {A : Type a} {B : Type b} {P : Pred A a′} {Q : Pred B b′}
    {f : A → B} (f′ : ∀[ P →̇ Q ∘ f ])
    {n : ℕ} {xs : Vec A n}
  → Any P xs → Any Q (f <$> xs)
any-ap         f′ {suc _} {_ ∷ _}  (fzero    , q) = fzero , f′ q
any-ap {P} {Q} f′ {suc n} {x ∷ xs} (fsuc idx , q) =
  bimap fsuc id (any-ap {P = P} {Q = Q} f′ {xs = xs} (idx , q))
