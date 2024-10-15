{-# OPTIONS --safe #-}
module Cat.Constructions.Types {ℓ} where

open import Cat.Prelude
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Morphism (Types ℓ) as Types

open import Data.Sum

open Biinv

biinv→equiv : {A B : Type ℓ} → A ≊ B → A ≃ B
biinv→equiv e .fst = e .to
biinv→equiv e .snd = qinv→is-equiv $ make-qinv (e .has-biinv .fst .retraction)
  (make-inverses (is-biinv→section-is-retraction (sym e .has-biinv)) (e .has-biinv .fst .is-retraction))

instance
  @0 Types-is-category : is-category (Types ℓ)
  Types-is-category .to-path e = ua (biinv→equiv e)
  Types-is-category .to-path-over p = ≊-pathᴾ refl (Types-is-category .to-path p)
    (fun-ext λ _ → =→ua-pathᴾ (biinv→equiv p) refl)

  Types-has-initial : Initial (Types ℓ)
  Types-has-initial .Initial.bot = ⊥
  Types-has-initial .Initial.has-⊥ _ .fst = λ ()
  Types-has-initial .Initial.has-⊥ _ .snd _ _ ()

  Types-has-terminal : Terminal (Types ℓ)
  Types-has-terminal .Terminal.top = ⊤
  Types-has-terminal .Terminal.has-⊤ _ = (λ _ → _) , (λ _ → refl)

Types-has-coproducts : Has-coproducts (Types ℓ)
Types-has-coproducts A B .Coproduct.coapex = A ⊎ₜ B
Types-has-coproducts A B .Coproduct.ι₁ = inl
Types-has-coproducts A B .Coproduct.ι₂ = inr
Types-has-coproducts A B .Coproduct.has-is-coproduct .is-coproduct.[_,_]₊ = [_,_]ᵤ
Types-has-coproducts A B .Coproduct.has-is-coproduct .is-coproduct.[]∘ι₁ = refl
Types-has-coproducts A B .Coproduct.has-is-coproduct .is-coproduct.[]∘ι₂ = refl
Types-has-coproducts A B .Coproduct.has-is-coproduct .is-coproduct.unique p q = []ᵤ-unique (p ⁻¹) (q ⁻¹) ⁻¹

Types-has-products : Has-products (Types ℓ)
Types-has-products A B .Product.apex = A ×ₜ B
Types-has-products A B .Product.π₁ = fst
Types-has-products A B .Product.π₂ = snd
Types-has-products A B .Product.has-is-product .is-product.⟨_,_⟩ₓ = <_,_>
Types-has-products A B .Product.has-is-product .is-product.π₁∘⟨⟩ = refl
Types-has-products A B .Product.has-is-product .is-product.π₂∘⟨⟩ = refl
Types-has-products A B .Product.has-is-product .is-product.unique p q = ext < p #_ , q #_ >
