{-# OPTIONS --safe #-}
module Meta.Effect.Idiom.Compose where

open import Foundations.Base

open import Meta.Marker
open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Effect.Idiom.Base
open import Meta.Effect.Idiom.Lawful

-- extracted to avoid circular dependencies via Marker

private variable ℓᵃ ℓᵇ ℓᶜ : Level

open Map ⦃ ... ⦄
open Idiom ⦃ ... ⦄
open Lawful-Idiom ⦃ ... ⦄

module _ {M N : Effect} (let module M = Effect M; module N = Effect N)
         ⦃ idm : Idiom M ⦄ ⦃ idn : Idiom N ⦄
         where

  open Idiom idm renaming (pure to pureₘ ; _<*>_ to _⊛ₘ_)
  open Idiom idn renaming (pure to pureₙ ; _<*>_ to _⊛ₙ_)

  Lawful-Idiom-Compose : Lawful-Idiom (eff M.₀)
                       → Lawful-Idiom (eff N.₀)
                       → Lawful-Idiom (eff (M.₀ ∘ N.₀)) ⦃ m = Idiom-Compose ⦄
  Lawful-Idiom-Compose lm ln .has-lawful-map =
    Lawful-Map-Compose (lm .Lawful-Idiom.has-lawful-map) (ln .Lawful-Idiom.has-lawful-map)
  Lawful-Idiom-Compose lm ln .pure-pres-app {f} {x} =
    ⌜ pureₘ _⊛ₙ_ ⊛ₘ pureₘ (pureₙ f) ⌝ ⊛ₘ pureₘ (pureₙ x)  ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    pureₘ (_⊛ₙ_ (pureₙ f)) ⊛ₘ pureₘ (pureₙ x)              ~⟨ lm .Lawful-Idiom.pure-pres-app ⟩
    pureₘ ⌜ pureₙ f ⊛ₙ pureₙ x ⌝                           ~⟨ ap! (ln .Lawful-Idiom.pure-pres-app) ⟩
    pureₘ (pureₙ (f x))                                    ∎
  Lawful-Idiom-Compose lm ln .pure-interchange {u} {v} =
    (pureₘ _⊛ₙ_) ⊛ₘ u ⊛ₘ pureₘ (pureₙ v)                              ~⟨ lm .Lawful-Idiom.pure-interchange ⟩
    (pureₘ (_$ pureₙ v)) ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ u)                       ~⟨ lm .Lawful-Idiom.pure-comp ⁻¹ ⟩
    ⌜ (pureₘ _∘ˢ_) ⊛ₘ (pureₘ (_$ pureₙ v)) ⌝ ⊛ₘ (pureₘ _⊛ₙ_) ⊛ₘ u     ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    ⌜ (pureₘ (λ f w → f w (pureₙ v))) ⊛ₘ (pureₘ _⊛ₙ_) ⌝ ⊛ₘ u          ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    (pureₘ ⌜ (_⊛ₙ (pureₙ v)) ⌝) ⊛ₘ u                                   ~⟨ ap! (fun-ext λ w → ln .Lawful-Idiom.pure-interchange) ⟩
    ⌜ pureₘ ((pureₙ (_$ v)) ⊛ₙ_) ⌝ ⊛ₘ u                                ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ (pureₘ (pureₙ (_$ v))) ⊛ₘ u                       ∎
  Lawful-Idiom-Compose lm ln .pure-comp {u} {v} {w} =
    -- likely not optimal, reduces both sides to `pureₘ foo ⊛ₘ u ⊛ₘ v ⊛ₘ w`

    (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ (pureₘ (pureₙ _∘ˢ_)) ⊛ₘ u) ⊛ₘ v) ⊛ₘ w           ~⟨ ap (λ q → (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ (q ⊛ₘ u) ⊛ₘ v) ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ ((pureₙ _∘ˢ_) ⊛ₙ_)) ⊛ₘ u) ⊛ₘ v) ⊛ₘ w                     ~⟨ ap (λ q → (pureₘ _⊛ₙ_) ⊛ₘ (q ⊛ₘ v) ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-comp ⁻¹) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ ((((pureₘ _∘ˢ_) ⊛ₘ (pureₘ _⊛ₙ_) ⊛ₘ (pureₘ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u) ⊛ₘ v) ⊛ₘ w   ~⟨ ap (λ q → (pureₘ _⊛ₙ_) ⊛ₘ (((q ⊛ₘ (pureₘ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u) ⊛ₘ v) ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ (((pureₘ (_∘ˢ_ (_⊛ₙ_))) ⊛ₘ (pureₘ ((_⊛ₙ_) (pureₙ _∘ˢ_))) ⊛ₘ u) ⊛ₘ v) ⊛ₘ w         ~⟨ ap (λ q → (pureₘ _⊛ₙ_) ⊛ₘ ((q ⊛ₘ u) ⊛ₘ v) ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((_⊛ₙ_) (pureₙ _∘ˢ_)))) ⊛ₘ u ⊛ₘ v) ⊛ₘ w                         ~⟨ ap (λ q → q ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-comp ⁻¹) ⟩
    ((pureₘ _∘ˢ_) ⊛ₘ (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u)) ⊛ₘ v ⊛ₘ w          ~⟨ ap (λ q → (q ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u)) ⊛ₘ v ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app) ⟩
    pureₘ (_⊛ₙ_ ∘ˢ_) ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u) ⊛ₘ v ⊛ₘ w                        ~⟨ ap (λ q → q ⊛ₘ v ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-comp ⁻¹) ⟩
    pureₘ _∘ˢ_ ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ_) ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_)) ⊛ₘ u ⊛ₘ v ⊛ₘ w                 ~⟨ ap (λ q → q ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_)) ⊛ₘ u ⊛ₘ v ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app) ⟩
    pureₘ ((_⊛ₙ_ ∘ˢ_) ∘ˢ_) ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_)) ⊛ₘ u ⊛ₘ v ⊛ₘ w                         ~⟨ ap (λ q → q ⊛ₘ u ⊛ₘ v ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app) ⟩
    pureₘ ((_⊛ₙ_ ∘ˢ_) ∘ˢ _⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_)) ⊛ₘ u ⊛ₘ v ⊛ₘ w                                      ~⟨ ap (λ q → pureₘ q ⊛ₘ u ⊛ₘ v ⊛ₘ w)
                                                                                                             (fun-ext λ α → fun-ext λ β → fun-ext λ γ → ln .Lawful-Idiom.pure-comp) ⟩
    pureₘ ((_$ _⊛ₙ_) ∘ˢ (_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⊛ₘ v ⊛ₘ w                                          ~⟨ ap (λ q → q ⊛ₘ u ⊛ₘ v ⊛ₘ w)
                                                                                                             (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ ((_$ _⊛ₙ_) ∘ˢ_) ⊛ₘ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⊛ₘ v ⊛ₘ w                              ~⟨ ap (λ q → q ⊛ₘ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ _∘ˢ_ ⊛ₘ pureₘ (_$ _⊛ₙ_) ⊛ₘ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⊛ₘ v ⊛ₘ w                      ~⟨ ap (λ q → q ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-comp) ⟩
    pureₘ (_$ _⊛ₙ_) ⊛ₘ (pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u) ⊛ₘ v ⊛ₘ w                                  ~⟨ ap (λ q → q ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-interchange ⁻¹) ⟩
    pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                                         ~⟨ ap (λ q → q ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ_) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                               ~⟨ ap (λ q → q ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ _∘ˢ_ ⊛ₘ pureₘ (_∘ˢ_ ∘ˢ _∘ˢ_) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                      ~⟨ ap (λ q → q ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-comp) ⟩
    pureₘ (_∘ˢ_ ∘ˢ _∘ˢ_) ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                                  ~⟨ ap (λ q → q ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ (_∘ˢ_ _∘ˢ_) ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                       ~⟨ ap (λ q → q ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ _∘ˢ_ ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                ~⟨ ap (λ q → q ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-comp) ⟩
    pureₘ _∘ˢ_ ⊛ₘ (pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u)) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                            ~⟨ ap (λ q → q ⊛ₘ w)
                                                                                                              (lm .Lawful-Idiom.pure-comp) ⟩
    pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ v) ⊛ₘ w                                          ~⟨ lm .Lawful-Idiom.pure-comp ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ u ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ v ⊛ₘ w)                                                      ∎

    -- using markers causes memory exhaustion
{-
    (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ _⊛ₙ_) ⊛ₘ (⌜ (pureₘ _⊛ₙ_) ⊛ₘ (pureₘ (pureₙ _∘ˢ_)) ⌝ ⊛ₘ u) ⊛ₘ v) ⊛ₘ w           ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ (⌜ (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ ((pureₙ _∘ˢ_) ⊛ₙ_)) ⊛ₘ u) ⌝ ⊛ₘ v) ⊛ₘ w                     ~⟨ ap! (lm .Lawful-Idiom.pure-comp ⁻¹) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ (((⌜ (pureₘ _∘ˢ_) ⊛ₘ (pureₘ _⊛ₙ_) ⌝ ⊛ₘ (pureₘ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u) ⊛ₘ v) ⊛ₘ w   ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    (pureₘ _⊛ₙ_) ⊛ₘ ((⌜ (pureₘ (_∘ˢ_ (_⊛ₙ_))) ⊛ₘ (pureₘ ((_⊛ₙ_) (pureₙ _∘ˢ_))) ⌝ ⊛ₘ u) ⊛ₘ v) ⊛ₘ w          ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    ⌜ (pureₘ _⊛ₙ_) ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((_⊛ₙ_) (pureₙ _∘ˢ_)))) ⊛ₘ u ⊛ₘ v) ⌝ ⊛ₘ w                         ~⟨ ap! (lm .Lawful-Idiom.pure-comp ⁻¹) ⟩
    (⌜ (pureₘ _∘ˢ_) ⊛ₘ (pureₘ _⊛ₙ_) ⌝ ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u)) ⊛ₘ v ⊛ₘ w          ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    ⌜ pureₘ (_⊛ₙ_ ∘ˢ_) ⊛ₘ ((pureₘ ((_⊛ₙ_) ∘ˢ ((pureₙ _∘ˢ_) ⊛ₙ_))) ⊛ₘ u) ⌝ ⊛ₘ v ⊛ₘ w                         ~⟨ ap! (lm .Lawful-Idiom.pure-comp ⁻¹) ⟩
    ⌜ pureₘ _∘ˢ_ ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ_) ⌝ ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_)) ⊛ₘ u ⊛ₘ v ⊛ₘ w                  ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    ⌜ pureₘ ((_⊛ₙ_ ∘ˢ_) ∘ˢ_) ⊛ₘ pureₘ (_⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_)) ⌝ ⊛ₘ u ⊛ₘ v ⊛ₘ w                          ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app) ⟩
    pureₘ ⌜ (_⊛ₙ_ ∘ˢ_) ∘ˢ _⊛ₙ_ ∘ˢ _⊛ₙ_ (pureₙ _∘ˢ_) ⌝ ⊛ₘ u ⊛ₘ v ⊛ₘ w                                         ~⟨ ap! (fun-ext λ α → fun-ext λ β → fun-ext λ γ →
                                                                                                                      ln .Lawful-Idiom.pure-comp) ⟩
    ⌜ pureₘ ((_$ _⊛ₙ_) ∘ˢ (_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⌝ ⊛ₘ u ⊛ₘ v ⊛ₘ w                                           ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    ⌜ pureₘ ((_$ _⊛ₙ_) ∘ˢ_) ⌝ ⊛ₘ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⊛ₘ v ⊛ₘ w                               ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    ⌜ pureₘ _∘ˢ_ ⊛ₘ pureₘ (_$ _⊛ₙ_) ⊛ₘ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u ⌝ ⊛ₘ v ⊛ₘ w                      ~⟨ ap! (lm .Lawful-Idiom.pure-comp) ⟩
    ⌜ pureₘ (_$ _⊛ₙ_) ⊛ₘ (pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⊛ₘ u) ⌝ ⊛ₘ v ⊛ₘ w                                  ~⟨ ap! (lm .Lawful-Idiom.pure-interchange ⁻¹) ⟩
    ⌜ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ _⊛ₙ_) ⌝ ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                                         ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    ⌜ pureₘ ((_∘ˢ_ ∘ˢ _∘ˢ_) ∘ˢ_) ⌝ ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ u ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                               ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    ⌜ pureₘ _∘ˢ_ ⊛ₘ pureₘ (_∘ˢ_ ∘ˢ _∘ˢ_) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ u ⌝ ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                      ~⟨ ap! (lm .Lawful-Idiom.pure-comp) ⟩
    ⌜ pureₘ (_∘ˢ_ ∘ˢ _∘ˢ_) ⌝ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                                  ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    ⌜ pureₘ (_∘ˢ_ _∘ˢ_) ⌝ ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                       ~⟨ ap! (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    ⌜ pureₘ _∘ˢ_ ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⌝ ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⊛ₘ w                ~⟨ ap! (lm .Lawful-Idiom.pure-comp) ⟩
    ⌜ pureₘ _∘ˢ_ ⊛ₘ (pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u)) ⊛ₘ pureₘ _⊛ₙ_ ⊛ₘ v ⌝ ⊛ₘ w                            ~⟨ ap! (lm .Lawful-Idiom.pure-comp) ⟩
    pureₘ _∘ˢ_ ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ u) ⊛ₘ (pureₘ _⊛ₙ_ ⊛ₘ v) ⊛ₘ w                                              ~⟨ lm .Lawful-Idiom.pure-comp ⟩
    ((pureₘ _⊛ₙ_) ⊛ₘ u) ⊛ₘ (((pureₘ _⊛ₙ_) ⊛ₘ v) ⊛ₘ w)                                                      ∎
-}
  Lawful-Idiom-Compose lm ln .map-pure {f} =
    map (map f)                         ~⟨ lm .Lawful-Idiom.map-pure ⟩
    pureₘ (map f) ⊛ₘ_                   ~⟨ ap (λ q → pureₘ q ⊛ₘ_) (ln .Lawful-Idiom.map-pure) ⟩
    pureₘ ((pureₙ f) ⊛ₙ_) ⊛ₘ_           ~⟨ ap (λ q → q ⊛ₘ_) (lm .Lawful-Idiom.pure-pres-app ⁻¹) ⟩
    pureₘ _⊛ₙ_ ⊛ₘ pureₘ (pureₙ f) ⊛ₘ_   ∎
