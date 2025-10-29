{-# OPTIONS --safe --no-exact-split #-}
module Order.Constructions.Lex.Bounded where

open import Cat.Prelude
open import Foundations.Base
open import Meta.Effect

open import Data.Empty
open import Data.Acc as Acc
open import Data.Dec as Dec
open import Data.Sum.Base as ⊎
open import Data.Sum.Path
open import Data.Nat.Base
open import Data.Nat.Order.Base renaming (_<_ to _<ℕ_)
open import Data.List
open import Data.List.Operations.Properties

open import Order.Constructions.Lex

private variable o ℓ o′ ℓ′ o″ ℓ″ ℓᵢ ℓⱼ ℓₖ : Level

-- TODO move

-- TODO maybe a Vec-like version would work better?
record List≤ {ℓ : Level} (A : 𝒰 ℓ) (n : ℕ) : 𝒰 ℓ where
  constructor _[<_>]
  field
    ls : List A
    prf : length ls ≤ n
open List≤ public

map≤ : {A : 𝒰 o} {B : 𝒰 o′} {n : ℕ}
     → (f : A → B)
     → List≤ A n → List≤ B n
map≤ f (xs [< prf >]) = (map f xs) [< =→≤ map-length ∙ prf >]

-- TODO other variants

-- strict

List≤-lex< : {A : 𝒰 o} {n : ℕ}
           → (_A<_ : A → A → 𝒰 ℓ)
           → List≤ A n → List≤ A n → 𝒰 (o ⊔ ℓ)
List≤-lex< _A<_ x y = List-lex< _A<_ (x .ls) (y .ls)

List≤-lex<-ind : {A : 𝒰 o} {_A<_ : A → A → 𝒰 ℓ} {n : ℕ}
               → (∀ {ℓ} {P : A → 𝒰 ℓ} → (∀ x → (∀ y → y A< x → P y) → P x) → ∀ x → P x)
               → ∀ {ℓ} {P : List≤ A n → 𝒰 ℓ} → (∀ xs → (∀ ys → List≤-lex< _A<_ ys xs → P ys) → P xs) → ∀ xs → P xs
List≤-lex<-ind                    ap     ih ([]       [< _ >])    = ih _ λ ys lt → absurd (lower lt)
List≤-lex<-ind        {n = zero}  ap     ih ((x ∷ xs) [< xprf >]) = absurd (s≰z xprf)
List≤-lex<-ind {_A<_} {n = suc n} ap {P} ih ((x ∷ xs) [< xprf >]) =
  ih ((x ∷ xs) [< xprf >]) λ where
                              ([] [< _ >])          _  → ih _ λ ys lt → absurd (lower lt)
                              ((y ∷ ys) [< yprf >]) →
                                 [ (λ y<x → go₁ x y<x ys yprf)
                                 , (λ where (y=x , ys<xs) → go₂ y xs (≤-peel xprf) (go₁ y) ys<xs yprf)
                                 ]ᵤ
  where
  go₂ : ∀ u w → (wprf : length w ≤ n)
              → (∀ {v} → v A< u → ∀ j → (prf : suc (length j) ≤ suc n) → P ((v ∷ j) [< prf >]))
              → ∀ {z} → List-lex< _A<_ z w → (zprf : suc (length z) ≤ suc n) → P ((u ∷ z) [< zprf >])
  go₂ u w wprf ih₁ =
    List≤-lex<-ind {n = n} ap
      {P = λ q → ∀ {z} → List-lex< _A<_ z (q .ls) → (zprf : suc (length z) ≤ suc n) → P ((u ∷ z) [< zprf >])}
      (λ xs ih₂ {z} z<xs zprf →
          ih ((u ∷ z) [< zprf >])
             λ where
             ([] [< _ >]) _  → ih _ λ qs lt → absurd (lower lt)
             ((j ∷ js) [< jprf >]) →
                [ (λ j<u → ih₁ j<u js jprf)
                , (λ where (j=u , js<z) →
                             subst (λ q → P ((q ∷ js) [< jprf >]))
                                   (j=u ⁻¹)
                                   (ih₂ (z [< ≤-peel zprf >]) z<xs js<z jprf))
                ]ᵤ)
      (w [< wprf >])

  go₁ : ∀ u {v} → v A< u → ∀ w → (prf : suc (length w) ≤ suc n) → P ((v ∷ w) [< prf >])
  go₁ =
    ap λ a ih₁ {v} v<a w wprf →
      ih ((v ∷ w) [< wprf >])
         λ where
             ([] [< _ >]) _  → ih _ λ qs lt → absurd (lower lt)
             ((z ∷ zs) [< zprf >]) →
                [ (λ z<v → ih₁ v v<a z<v zs zprf)
                , (λ where (z=v , zs<w) →
                              go₂ z w (≤-peel wprf)
                                (subst (λ q → ∀ {z} → z A< q → ∀ w → (wprf : suc (length w) ≤ suc n) → P ((z ∷ w) [< wprf >]))
                                       (z=v ⁻¹)
                                       λ {q} → ih₁ v v<a {q})
                                zs<w zprf)
                ]ᵤ

List≤-lex<-wf : {A : 𝒰 o} {_A<_ : A → A → 𝒰 ℓ} {n : ℕ}
              → is-wf _A<_
              → is-wf (List≤-lex< {n = n} _A<_)
List≤-lex<-wf wa =
  from-induction λ P → List≤-lex<-ind (λ {_} {P} → to-induction wa P)
