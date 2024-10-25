{-# OPTIONS --safe #-}
module Cat.Constructions.n-Types {ℓ} n where

open import Cat.Prelude
open import Cat.Constructions.Types
open import Cat.Diagram.Initial
open import Cat.Diagram.Terminal
open import Cat.Functor.Equivalence
open import Cat.Functor.FullSubcategory

open Functor

instance
  @0 n-Types-is-category : is-category (n-Types ℓ n)
  n-Types-is-category = iso-restrict→is-category (is-of-hlevel n) go
    (make-precat-iso (qinv→is-equiv (qinv (el $ₜ²_) refl refl)) id-is-equiv)
    Types-is-category
    where
    go : n-Types ℓ n ⇒ Restrict {C = Types ℓ} (is-of-hlevel n)
    go .F₀ (el X p) = X , p
    go .F₁ f = f
    go .F-id = refl
    go .F-∘ _ _ = refl

  n-Types-has-initial : ⦃ _ : n ≥ʰ 1 ⦄ → Initial (n-Types ℓ n)
  n-Types-has-initial ⦃ s≤ʰs _ ⦄ .Initial.bot = ⊥
  n-Types-has-initial ⦃ s≤ʰs _ ⦄ .Initial.has-⊥ _ .fst = λ ()
  n-Types-has-initial ⦃ s≤ʰs _ ⦄ .Initial.has-⊥ _ .snd _ _ ()

  n-Types-has-terminal : Terminal (n-Types ℓ n)
  n-Types-has-terminal .Terminal.top = ⊤
  n-Types-has-terminal .Terminal.has-⊤ _ .fst _ = _
  n-Types-has-terminal .Terminal.has-⊤ _ .snd _ = refl
