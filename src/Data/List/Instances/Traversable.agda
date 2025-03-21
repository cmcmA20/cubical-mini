{-# OPTIONS --safe #-}
module Data.List.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Effect.Idiom
open import Meta.Effect.Traversable
open import Meta.Effect.Traversable.Lawful

open import Data.List.Base

open Map ⦃ ... ⦄
open Idiom ⦃ ... ⦄
open Traversable ⦃ ... ⦄
open Lawful-Map ⦃ ... ⦄
open Lawful-Idiom ⦃ ... ⦄
open Lawful-Traversable ⦃ ... ⦄

private variable ℓᵃ ℓᵇ ℓᶜ : Level

list-traverse : {A : Type ℓᵃ} {B : Type ℓᵇ} {M : Effect} ⦃ i : Idiom M ⦄
              → let module M = Effect M in
                (A → M.₀ B) → List A → M.₀ (List B)
list-traverse f []       = pure []
list-traverse f (x ∷ xs) = ⦇ f x ∷ list-traverse f xs ⦈

list-traverse-id : {A : Type ℓᵃ} (xs : List A)
                 → list-traverse ⦃ i = Idiom-Id ⦄ id xs ＝ xs
list-traverse-id []       = refl
list-traverse-id (x ∷ xs) = ap (x ∷_) (list-traverse-id xs)

list-traverse-comp : {M N : Effect}
                     ⦃ mi : Idiom M ⦄ (let module M = Effect M)
                     ⦃ ni : Idiom N ⦄ (let module N = Effect N)
                     ⦃ lm : Lawful-Idiom M ⦄ ⦃ ln : Lawful-Idiom N ⦄
                     {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
                     {f : A → M.₀ B} {g : B → N.₀ C}
                     (xs : List A)
                   → list-traverse ⦃ i = Idiom-Compose ⦄ (map g ∘ f) xs ＝
                     map (list-traverse g) (list-traverse f xs)
list-traverse-comp ⦃ mi ⦄ {g} [] =
    mi .pure-pres-app ⁻¹
  ∙ happly (mi .map-pure {f = list-traverse g} ⁻¹) (pure [])
list-traverse-comp ⦃ mi ⦄ ⦃ ni ⦄ {f} {g} (x ∷ xs) =
  pureₘ _⊛ₙ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ pureₘ (pureₙ _∷_) ⊛ₘ mapₘ g (f x)) ⊛ₘ list-traverse ⦃ i = Idiom-Compose ⦄ (mapₘ g ∘ f) xs
    ~⟨ ap (λ q → pureₘ _⊛ₙ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ pureₘ (pureₙ _∷_) ⊛ₘ mapₘ g (f x)) ⊛ₘ q) (list-traverse-comp xs) ⟩
  pureₘ _⊛ₙ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ pureₘ (pureₙ _∷_) ⊛ₘ mapₘ g (f x)) ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)
    ~⟨ ap (λ q → pureₘ _⊛ₙ_ ⊛ₘ (q ⊛ₘ mapₘ g (f x)) ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)) (mi .pure-pres-app) ⟩
  pureₘ _⊛ₙ_ ⊛ₘ (pureₘ ((pureₙ _∷_) ⊛ₙ_) ⊛ₘ mapₘ g (f x)) ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)
    ~⟨ ap (λ q → pureₘ _⊛ₙ_ ⊛ₘ q ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)) (happly (mi .map-pure ⁻¹) (mapₘ g (f x))) ⟩
  pureₘ _⊛ₙ_ ⊛ₘ mapₘ ((pureₙ _∷_) ⊛ₙ_) (mapₘ g (f x)) ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)
    ~⟨ ap (λ q → q ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)) (happly (mi .map-pure ⁻¹) (mapₘ ((pureₙ _∷_) ⊛ₙ_) (mapₘ g (f x)))) ⟩
  mapₘ _⊛ₙ_ (mapₘ (pureₙ _∷_ ⊛ₙ_) (mapₘ g (f x))) ⊛ₘ mapₘ (list-traverse g) (list-traverse f xs)
    ~⟨ map-<*>-precomp ⁻¹ ⟩
  mapₘ (_∘ list-traverse g) (mapₘ _⊛ₙ_ (mapₘ ((pureₙ _∷_) ⊛ₙ_) (mapₘ g (f x)))) ⊛ₘ list-traverse f xs
    ~⟨ ap (λ q → mapₘ (_∘ list-traverse g) (mapₘ _⊛ₙ_ q) ⊛ₘ list-traverse f xs) (happly map-pres-comp (f x) ⁻¹) ⟩
  mapₘ (_∘ list-traverse g) (mapₘ _⊛ₙ_ (mapₘ (((pureₙ _∷_) ⊛ₙ_) ∘ g) (f x))) ⊛ₘ list-traverse f xs
    ~⟨ ap (λ q → mapₘ (_∘ list-traverse g) q ⊛ₘ list-traverse f xs) (happly map-pres-comp (f x) ⁻¹) ⟩
  mapₘ (_∘ list-traverse g) (mapₘ (_⊛ₙ_ ∘ (λ z → pureₙ _∷_ ⊛ₙ g z)) (f x)) ⊛ₘ list-traverse f xs
    ~⟨ ap (λ q → q ⊛ₘ list-traverse f xs) (happly map-pres-comp (f x) ⁻¹) ⟩
  mapₘ ((list-traverse g ∘_) ∘ _∷_) (f x) ⊛ₘ list-traverse f xs
    ~⟨ ap (λ q → q ⊛ₘ list-traverse f xs) (happly map-pres-comp (f x)) ⟩
  mapₘ (list-traverse g ∘_) (mapₘ _∷_ (f x)) ⊛ₘ list-traverse f xs
    ~⟨ map-<*> ⁻¹ ⟩
  mapₘ (list-traverse g) (mapₘ _∷_ (f x) ⊛ₘ list-traverse f xs)
    ~⟨ ap (λ q → mapₘ (list-traverse g) (q ⊛ₘ list-traverse f xs)) (happly (mi .map-pure) (f x)) ⟩
  mapₘ (list-traverse g) (pureₘ _∷_ ⊛ₘ f x ⊛ₘ list-traverse f xs)
    ∎
  where
  open Map (mi .Map-idiom) renaming (map to mapₘ)
  open Idiom mi renaming (pure to pureₘ ; _<*>_ to _⊛ₘ_)
  open Idiom ni renaming (pure to pureₙ ; _<*>_ to _⊛ₙ_)

instance
  Traversable-List : Traversable (eff List)
  Traversable-List .traverse = list-traverse

  Lawful-Traversable-List : Lawful-Traversable (eff List)
  Lawful-Traversable-List .traverse-id = fun-ext list-traverse-id
  Lawful-Traversable-List .traverse-comp = fun-ext list-traverse-comp
