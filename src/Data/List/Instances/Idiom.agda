{-# OPTIONS --safe #-}
module Data.List.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map

open import Data.List.Base
open import Data.List.Instances.Map
open import Data.List.Properties

private variable
  ℓ : Level
  A B C : Type ℓ

open Map ⦃ ... ⦄
open Lawful-Map ⦃ ... ⦄
open Idiom ⦃ ... ⦄
open Lawful-Idiom ⦃ ... ⦄

_<*>ₗ_ : List (A → B) → List A → List B
[]       <*>ₗ xs = []
(f ∷ fs) <*>ₗ xs = map f xs ++ (fs <*>ₗ xs)

<*>ₗ-++-app
  : (fs gs : List (A → B)) (xs : List A)
  → ((fs ++ gs) <*>ₗ xs) ＝ (fs <*>ₗ xs) ++ (gs <*>ₗ xs)
<*>ₗ-++-app []       _  _  = refl
<*>ₗ-++-app (f ∷ fs) gs xs
  = ap (map f xs ++_) (<*>ₗ-++-app fs gs xs)
  ∙ ++-assoc (map f xs) (fs <*>ₗ xs) _ ⁻¹

map-precomp-<*>ₗ
  : (g : B → C) (fs : List (A → B)) (xs : List A)
  → mapₗ g (fs <*>ₗ xs) ＝ (mapₗ (g ∘ˢ_) fs <*>ₗ xs)
map-precomp-<*>ₗ g []       xs = refl
map-precomp-<*>ₗ g (f ∷ fs) xs
  = map-++ g (mapₗ f xs) _
  ∙ ap (_++ mapₗ g (fs <*>ₗ xs)) (map-pres-comp # xs) ⁻¹
  ∙ ap (mapₗ _ xs ++_) (map-precomp-<*>ₗ g fs xs)

instance
  Idiom-List : Idiom (eff List)
  Idiom-List .pure = _∷ []
  Idiom-List ._<*>_ = _<*>ₗ_

  Lawful-Idiom-List : Lawful-Idiom (eff List)
  Lawful-Idiom-List .pure-pres-app = refl
  Lawful-Idiom-List .pure-interchange {A} {B} {u} {v} = go u v where opaque
    go : (fs : List (A → B)) (x : A) → (fs <*> pure x) ＝ (pure (_$ x) <*> fs)
    go []       x = refl
    go (f ∷ fs) x = ap (_ ∷_) (go fs x)
  Lawful-Idiom-List .pure-comp {A} {B} {C} {u} {v} {w} = go u v w where opaque
    go : (gs : List (B → C)) (fs : List (A → B)) (xs : List A)
       → (pure _∘ˢ_ <*> gs <*> fs <*> xs) ＝ (gs <*> (fs <*> xs))
    go []       _  _  = refl
    go (g ∷ gs) fs xs =
      pure _∘ˢ_ <*> g ∷ gs <*> fs <*> xs
        ~⟨ <*>ₗ-++-app (map (g ∘ˢ_) fs) _ xs ⟩
      (map (g ∘ˢ_) fs <*> xs) ++ (((map _∘ˢ_ gs ++ []) <*> fs) <*> xs)
        ~⟨ ap (_++ ((((map _∘ˢ_ gs ++ []) <*> fs) <*> xs))) (map-precomp-<*>ₗ g fs _) ⟨
      map g (fs <*> xs) ++ (pure _∘ˢ_ <*> gs <*> fs <*> xs)
        ~⟨ ap (map g (fs <*> xs) ++_) (go gs fs xs) ⟩
      map g (fs <*> xs) ++ (gs <*> (fs <*> xs)) ∎
  Lawful-Idiom-List .map-pure = fun-ext λ _ → ++-id-r _ ⁻¹
