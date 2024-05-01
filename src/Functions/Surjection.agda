{-# OPTIONS --safe #-}
module Functions.Surjection where

open import Meta.Prelude
open import Meta.Effect.Bind

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

  Reflexive-Split-surj :  Reflexive (_↠!_ {ℓ})
  Reflexive-Split-surj .refl = refl , (_, refl)

  Reflexive-Surj :  Reflexive (_↠_ {ℓ})
  Reflexive-Surj .refl = refl , λ a → ∣ a , refl ∣₁

  Transitive-Split-surj : Transitive (_↠!_ {ℓ} {ℓ′}) (_↠!_ {ℓ′ = ℓ″}) _↠!_
  Transitive-Split-surj ._∙_ (f , _) (g , _) .fst = f ∙ g
  Transitive-Split-surj ._∙_ (f , φ) (g , ψ) .snd c =
    let u  , v  = ψ c
        u′ , v′ = φ u
    in u′ , ap g v′ ∙ v

  Transitive-Surj : Transitive (_↠_ {ℓ} {ℓ′}) (_↠_ {ℓ′ = ℓ″}) _↠_
  Transitive-Surj ._∙_ (f , _) (g , _) .fst = f ∙ g
  Transitive-Surj ._∙_ (f , φ) (g , ψ) .snd c = do
    u  , v  ← ψ c
    u′ , v′ ← φ u
    pure (u′ , ap g v′ ∙ v)

is-left-inverse-of→is-surjective : f is-left-inverse-of g → is-surjective f
is-left-inverse-of→is-surjective {g} s b = ∣ g b , s b ∣₁

is-equiv→is-surjective : is-equiv f → is-surjective f
is-equiv→is-surjective r y = ∣ equiv-proof r y .fst ∣₁
