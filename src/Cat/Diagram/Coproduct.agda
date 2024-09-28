{-# OPTIONS --safe #-}
module Cat.Diagram.Coproduct where

open import Cat.Prelude
open import Cat.Constructions.Product
import Cat.Morphism

private variable o h : Level

module _ (C : Precategory o h) where
  open Cat.Morphism C

  record is-coproduct {A B P : Ob} (ι₁ : A ⇒ P) (ι₂ : B ⇒ P) : 𝒰 (o ⊔ h) where
    no-eta-equality
    field
      [_,_]₊ : {Q : Ob} (f : A ⇒ Q) (g : B ⇒ Q) → P ⇒ Q
      []∘ι₁  : {Q : Ob} {f : A ⇒ Q} {g : B ⇒ Q} → [ f , g ]₊ ∘ ι₁ ＝ f
      []∘ι₂  : {Q : Ob} {f : A ⇒ Q} {g : B ⇒ Q} → [ f , g ]₊ ∘ ι₂ ＝ g

      unique : {Q : Ob} {f : A ⇒ Q} {g : B ⇒ Q}
               {h : P ⇒ Q}
             → (le : h ∘ ι₁ ＝ f) (ri : h ∘ ι₂ ＝ g)
             → h ＝ [ f , g ]₊

    unique₂ : {Q : Ob} {f : A ⇒ Q} {g : B ⇒ Q}
            → {h₁ : P ⇒ Q} (le₁ : h₁ ∘ ι₁ ＝ f) (ri₁ : h₁ ∘ ι₂ ＝ g)
            → {h₂ : P ⇒ Q} (le₂ : h₂ ∘ ι₁ ＝ f) (ri₂ : h₂ ∘ ι₂ ＝ g)
            → h₁ ＝ h₂
    unique₂ le₁ ri₁ le₂ ri₂ = unique le₁ ri₁ ∙ sym (unique le₂ ri₂)


  record Coproduct (A B : Ob) : 𝒰 (o ⊔ h) where
    no-eta-equality
    field
      coapex : Ob
      ι₁ : A ⇒ coapex
      ι₂ : B ⇒ coapex
      has-is-coproduct : is-coproduct ι₁ ι₂

    open is-coproduct has-is-coproduct public

-- TODO see if it's of any use for instance search
Has-coproducts : Precategory o h → 𝒰 (o ⊔ h)
Has-coproducts C = ∀ x y → Coproduct C x y

module _ {C : Precategory o h} where
  open Cat.Morphism C

  private variable A B : Ob

  ⊎-unique : (c₁ c₂ : Coproduct C A B) → Coproduct.coapex c₁ ≅ Coproduct.coapex c₂
  ⊎-unique c₁ c₂ = iso c₁→c₂ c₂→c₁ c₁→c₂→c₁ c₂→c₁→c₂
    where
      module c₁ = Coproduct c₁
      module c₂ = Coproduct c₂

      c₁→c₂ : c₁.coapex ⇒ c₂.coapex
      c₁→c₂ = c₁.[ c₂.ι₁ , c₂.ι₂ ]₊

      c₂→c₁ : c₂.coapex ⇒ c₁.coapex
      c₂→c₁ = c₂.[ c₁.ι₁ , c₁.ι₂ ]₊

      c₁→c₂→c₁ : c₁→c₂ ∘ c₂→c₁ ＝ id
      c₁→c₂→c₁ = c₂.unique₂
        (assoc _ _ _ ∙ (c₂.[]∘ι₁ ▷ _) ∙ c₁.[]∘ι₁)
        (assoc _ _ _ ∙ (c₂.[]∘ι₂ ▷ _) ∙ c₁.[]∘ι₂)
        (id-l _) (id-l _)

      c₂→c₁→c₂ : c₂→c₁ ∘ c₁→c₂ ＝ id
      c₂→c₁→c₂ = c₁.unique₂
        (assoc _ _ _ ∙ (c₁.[]∘ι₁ ▷ _) ∙ c₂.[]∘ι₁)
        (assoc _ _ _ ∙ (c₁.[]∘ι₂ ▷ _) ∙ c₂.[]∘ι₂)
        (id-l _) (id-l _)


  module Binary-coproducts (all-coproducts : Has-coproducts C) where
    module coproducts {A} {B} = Coproduct (all-coproducts A B)

    open coproducts renaming (unique to []-unique) public

    instance
      ⊎-Ob : ⊎-notation Ob Ob Ob
      ⊎-Ob .⊎-notation.Constraint _ _ = ⊤
      ⊎-Ob ._⊎_ A B = coapex {A} {B}
      {-# OVERLAPPING ⊎-Ob #-}

      ⊎-Hom : {A B X Y : Ob} → ⊎-notation (A ⇒ X) (B ⇒ Y) (A ⊎ B ⇒ X ⊎ Y)
      ⊎-Hom .⊎-notation.Constraint _ _ = ⊤
      ⊎-Hom ._⊎_ f g = [ ι₁ ∘ f , ι₂ ∘ g ]₊
      {-# OVERLAPPING ⊎-Hom #-}

    ∇ : {A : Ob} → A ⊎ A ⇒ A
    ∇ = [ id , id ]₊

    coswap : {A B : Ob} → A ⊎ B ⇒ B ⊎ A
    coswap = [ ι₂ , ι₁ ]₊

    ⊎-assoc : {A B C : Ob} → A ⊎ (B ⊎ C) ⇒ (A ⊎ B) ⊎ C
    ⊎-assoc = [ ι₁ ∘ ι₁ , [ ι₁ ∘ ι₂ , ι₂ ]₊ ]₊

    -- open Functor
    -- ⊎ᶠ : C × C ⇒ C
    -- ⊎ᶠ .F₀ (A , B) = A ⊎ B
    -- ⊎ᶠ .F₁ (f , g) = f ⊎ g
    -- ⊎ᶠ .F-id = sym $ coproducts.unique (id-l _ ∙ id-r _ ⁻¹) (id-l _ ∙ id-r _ ⁻¹)
    -- ⊎ᶠ .F-∘ (f , g) (h , i) = sym $ coproducts.unique
    --   (assoc _ _ _ ⁻¹ ∙ (coproducts.[]∘ι₁ ▷ _) ∙ assoc _ _ _ ∙ (_ ◁ coproducts.[]∘ι₁) ∙ assoc _ _ _ ⁻¹)
    --   (assoc _ _ _ ⁻¹ ∙ (coproducts.[]∘ι₂ ▷ _) ∙ assoc _ _ _ ∙ (_ ◁ coproducts.[]∘ι₂) ∙ assoc _ _ _ ⁻¹)
