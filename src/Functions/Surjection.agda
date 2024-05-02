{-# OPTIONS --safe #-}
module Functions.Surjection where

open import Meta.Prelude
open import Meta.Effect.Bind
open import Meta.Extensionality

open import Functions.Embedding

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Bind

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  g : B → A

Split-surjective : (A → B) → Type _
Split-surjective {B} f = Π[ y ꞉ B ] fibre f y

_↠!_ : Type ℓ → Type ℓ′ → Type _
A ↠! B = Σ[ f ꞉ (A → B) ] Split-surjective f

is-surjective : (A → B) → Type _
is-surjective {B} f = Π[ y ꞉ B ] ∥ fibre f y ∥₁

is-surjective-is-prop : is-prop (is-surjective f)
is-surjective-is-prop = hlevel 1

_↠_ : Type ℓ → Type ℓ′ → Type _
A ↠ B = Σ[ f ꞉ (A → B) ] is-surjective f

instance
  Funlike-Split-surj : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (A ↠! B) A (λ _ → B)
  Funlike-Split-surj ._#_ = fst

  Funlike-Surj : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (A ↠ B) A (λ _ → B)
  Funlike-Surj ._#_ = fst

  Refl-Split-surj :  Refl (_↠!_ {ℓ})
  Refl-Split-surj .refl = refl , (_, refl)

  Refl-Surj :  Refl (_↠_ {ℓ})
  Refl-Surj .refl = refl , λ a → ∣ a , refl ∣₁

  Trans-Split-surj : Trans (_↠!_ {ℓ} {ℓ′}) (_↠!_ {ℓ′ = ℓ″}) _↠!_
  Trans-Split-surj ._∙_ (f , _) (g , _) .fst = f ∙ g
  Trans-Split-surj ._∙_ (f , φ) (g , ψ) .snd c =
    let u  , v  = ψ c
        u′ , v′ = φ u
    in u′ , ap g v′ ∙ v

  Trans-Surj : Trans (_↠_ {ℓ} {ℓ′}) (_↠_ {ℓ′ = ℓ″}) _↠_
  Trans-Surj ._∙_ (f , _) (g , _) .fst = f ∙ g
  Trans-Surj ._∙_ (f , φ) (g , ψ) .snd c = do
    u  , v  ← ψ c
    u′ , v′ ← φ u
    pure (u′ , ap g v′ ∙ v)

is-left-inverse-of→is-surjective : f is-left-inverse-of g → is-surjective f
is-left-inverse-of→is-surjective {g} s b = ∣ g b , s b ∣₁

is-equiv→is-surjective : is-equiv f → is-surjective f
is-equiv→is-surjective r y = ∣ equiv-proof r y .fst ∣₁

instance
  Extensional-↠
    : {A : Type ℓ} ⦃ sb : Extensional (A → B) ℓ″ ⦄
    → Extensional (A ↠ B) ℓ″
  Extensional-↠ ⦃ sb ⦄ = Σ-prop→extensional! sb
