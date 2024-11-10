{-# OPTIONS --safe #-}
module Meta.Effect.Idiom.Lawful where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom.Base
open import Meta.Effect.Map

private variable ℓᵃ ℓᵇ ℓᶜ : Level

open Idiom ⦃ ... ⦄

record Lawful-Idiom (M : Effect) ⦃ m : Idiom M ⦄ : Typeω where
  private module M = Effect M
  open Map ⦃ ... ⦄
  field
    ⦃ has-lawful-map ⦄ : Lawful-Map M
    pure-id
      : {A : Type ℓᵃ} {v : M.₀ A}
      → (pure id <*> v) ＝ v
    pure-pres-app
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {f : A → B} {x : A}
      → Path (M.₀ B) (pure f <*> pure x) (pure (f x))
    pure-interchange
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {u : M.₀ (A → B)} {v : A}
      → Path (M.₀ B) (u <*> pure v) (pure (_$ v) <*> u)
    pure-comp
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {u : M.₀ (B → C)} {v : M.₀ (A → B)} {w : M.₀ A}
      → Path (M.₀ C) (pure _∘ˢ_ <*> u <*> v <*> w) (u <*> (v <*> w))
    map-pure -- TODO check if it's provable
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {f : A → B}
      → Path (M.₀ A → M.₀ B) (map f) (λ x → pure f <*> x)

  open Lawful-Map ⦃ ... ⦄
  opaque
    map-<*>
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {f : B → C} {u : M.₀ (A → B)} {v : M.₀ A}
      → map f (u <*> v) ＝ (map (f ∘_) u <*> v)
    map-<*> {f} {u} {v} =
      map f (u <*> v)                   ~⟨ map-pure # (u <*> v) ⟩
      pure f <*> (u <*> v)              ~⟨ pure-comp ⟨
      pure _∘ˢ_ <*> pure f <*> u <*> v  ~⟨ ap (λ φ → φ <*> u <*> v) pure-pres-app ⟩
      _ <*> u <*> v                     ~⟨ ap (_<*> v) (map-pure # u) ⟨
      map (f ∘_) u <*> v                ∎

    map-<*>-precomp
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {f : A → B} {u : M.₀ (B → C)} {v : M.₀ A}
      → (map (_∘ f) u <*> v) ＝ (u <*> map f v)
    map-<*>-precomp {f} {u} {v} =
      map (_∘ f) u <*> v                     ~⟨ ap (_<*> v) (map-pres-comp # u) ⟩
      map (λ k → k f) (map _∘ˢ_ u) <*> v     ~⟨ ap (_<*> v) (map-pure # (map _∘ˢ_ u)) ⟩
      pure (λ k → k f) <*> map _∘ˢ_ u <*> v  ~⟨ ap (_<*> v) pure-interchange ⟨
      map _∘ˢ_ u <*> pure f <*> v            ~⟨ ap (λ φ → φ <*> pure f <*> v) (map-pure # _) ⟩
      pure _∘ˢ_ <*> u <*> pure f <*> v       ~⟨ pure-comp ⟩
      u <*> (pure f <*> v)                   ~⟨ ap (u <*>_) (map-pure # v) ⟨
      u <*> map f v                          ∎
