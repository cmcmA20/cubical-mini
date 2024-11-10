{-# OPTIONS --safe #-}
module Meta.Effect.Bind.Lawful where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Bind.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map

private variable ℓᵃ ℓᵇ ℓᶜ : Level

open Bind ⦃ ... ⦄
open Idiom ⦃ ... ⦄

record Lawful-Bind (M : Effect) ⦃ m : Bind M ⦄ : Typeω where
  private module M = Effect M
  field
    ⦃ has-lawful-idiom ⦄ : Lawful-Idiom M
    >>=-id-l
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {x : A} {f : A → M.₀ B}
      → (pure x >>= f) ＝ f x
    >>=-id-r
      : {A : Type ℓᵃ} {mx : M.₀ A}
      → (mx >>= pure) ＝ mx
    >>=-assoc
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {mx : M.₀ A} {f : A → M.₀ B} {g : B → M.₀ C}
      → (mx >>= f >>= g) ＝ (mx >>= λ x → f x >>= g)
    <*>->>=
      : {A : Type ℓᵃ} {B : Type ℓᵇ}
        {mf : M.₀ (A → B)} {mx : M.₀ A}
      → (mf <*> mx) ＝ (mf >>= λ f → mx >>= (pure ∘ f))

  open Map ⦃ ... ⦄
  open Lawful-Idiom ⦃ ... ⦄

  opaque
    map->>=-pure
      : {A : Type ℓᵃ} {B : Type ℓᵇ}
        {f : A → B} {mx : M.₀ A}
      → map f mx ＝ (mx >>= (pure ∘ f))
    map->>=-pure {f} {mx} =
      map f mx                            ~⟨ map-pure # mx ⟩
      pure f <*> mx                       ~⟨ <*>->>= ⟩
      (pure f >>= λ f → mx >>= pure ∘ f)  ~⟨ >>=-id-l ⟩
      (mx >>= f ∙ pure)                   ∎

    map->>=
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {f : A → B} {g : B → M.₀ C} {mx : M.₀ A}
      → (map f mx >>= g) ＝ (mx >>= (g ∘ f))
    map->>= {f} {g} {mx} =
      (map f mx >>= g)                   ~⟨ ap (_>>= g) map->>=-pure ⟩
      (mx >>= pure ∘ f >>= g)            ~⟨ >>=-assoc ⟩
      (mx >>= (λ x → pure (f x) >>= g))  ~⟨ ap (mx >>=_) (fun-ext (λ _ → >>=-id-l)) ⟩
      (mx >>= g ∘ f)                     ∎
