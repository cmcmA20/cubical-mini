{-# OPTIONS --safe #-}
module Meta.Effect.Map.Lawful where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Container
open import Meta.Effect.Map.Base

open import Data.Container.Instances.Brackets

private variable
  ℓ ℓa ℓb ℓc : Level
  A B : Type ℓ

open Map ⦃ ... ⦄

record Lawful-Map (M : Effect) ⦃ m : Map M ⦄ : Typeω where
  private module M = Effect M
  field
    map-pres-id
      : {A : Type ℓa}
      → Path (M.₀ A → M.₀ A) (map id) id
    map-pres-comp
      : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
        {f : A → B} {g : B → C}
      → Path (M.₀ A → M.₀ C) (map (f ∙ g)) (map f ∙ map g)


module _ {M : Effect} ⦃ ac : Abstract-Container M ⦄ where
  private module M = Effect M
  open Abstract-Container ac renaming (has-abs-con to e)
  open Lawful-Map ⦃ ... ⦄

  mapᶜ : (f : A → B) → ⟦ con ⟧ A → ⟦ con ⟧ B
  mapᶜ f = second (f ∘_)

  instance
    Map-AC-default : Map M
    Map-AC-default .map f mx = e ⁻¹ $ mapᶜ f (e $ mx)
    {-# INCOHERENT Map-AC-default #-}

  opaque
    Lawful-Map-AC
      : ⦃ m : Map M ⦄
        (p : ∀ {ℓa ℓb : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
           → (f : A → B) → m .map f ＝ Map-AC-default .map f)
      → Lawful-Map M
    Lawful-Map-AC p .map-pres-id = p id ∙ Equiv.ε (e ⁻¹)
    Lawful-Map-AC ⦃ m ⦄ p .map-pres-comp {A} {f} {g} =
      m .map (f ∙ g)                                 ~⟨ p (f ∙ g) ⟩
      (λ mx → e ⁻¹ $ mapᶜ g (mapᶜ f (e $ mx)))       ~⟨ (((λ z → mapᶜ f (e $ z)) ◁ Equiv.ε e ⁻¹) ▷ mapᶜ g) ▷ is-equiv→inverse (e .snd)  ⟩
      Map-AC-default .map f ∙ Map-AC-default .map g  ~⟨ (p f ▷ m .map g) ∙ (_ ◁ p g) ⟨
      m .map f ∙ m .map g                            ∎
