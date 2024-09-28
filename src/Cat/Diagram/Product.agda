{-# OPTIONS --safe #-}
module Cat.Diagram.Product where

open import Cat.Prelude
open import Cat.Constructions.Product
import Cat.Morphism

private variable o h : Level

module _ (C : Precategory o h) where
  open Cat.Morphism C

  record is-product {A B P : Ob} (π₁ : P ⇒ A) (π₂ : P ⇒ B) : 𝒰 (o ⊔ h) where
    no-eta-equality
    field
      ⟨_,_⟩ₓ : {Q : Ob} (f : Q ⇒ A) (g : Q ⇒ B) → Q ⇒ P
      π₁∘⟨⟩  : {Q : Ob} {f : Q ⇒ A} {g : Q ⇒ B} → π₁ ∘ ⟨ f , g ⟩ₓ ＝ f
      π₂∘⟨⟩  : {Q : Ob} {f : Q ⇒ A} {g : Q ⇒ B} → π₂ ∘ ⟨ f , g ⟩ₓ ＝ g

      unique : {Q : Ob} {f : Q ⇒ A} {g : Q ⇒ B}
               {h : Q ⇒ P}
             → (fs : π₁ ∘ h ＝ f) (sn : π₂ ∘ h ＝ g)
             → h ＝ ⟨ f , g ⟩ₓ

    unique₂ : {Q : Ob} {f : Q ⇒ A} {g : Q ⇒ B}
            → {h₁ : Q ⇒ P} (fs₁ : π₁ ∘ h₁ ＝ f) (sn₁ : π₂ ∘ h₁ ＝ g)
            → {h₂ : Q ⇒ P} (fs₂ : π₁ ∘ h₂ ＝ f) (sn₂ : π₂ ∘ h₂ ＝ g)
            → h₁ ＝ h₂
    unique₂ fs₁ sn₁ fs₂ sn₂ = unique fs₁ sn₁ ∙ sym (unique fs₂ sn₂)

    ⟨⟩∘ : {Q R : Ob} {f : Q ⇒ A} {g : Q ⇒ B} (h : R ⇒ Q)
        → ⟨ f , g ⟩ₓ ∘ h ＝ ⟨ f ∘ h , g ∘ h ⟩ₓ
    ⟨⟩∘ f = unique (sym (assoc _ _ _) ∙ (_ ◁ π₁∘⟨⟩)) (sym (assoc _ _ _) ∙ (_ ◁ π₂∘⟨⟩))

    ⟨⟩-η : ⟨ π₁ , π₂ ⟩ₓ ＝ id
    ⟨⟩-η = sym $ unique (id-r _) (id-r _)


  record Product (A B : Ob) : 𝒰 (o ⊔ h) where
    no-eta-equality
    field
      apex : Ob
      π₁ : apex ⇒ A
      π₂ : apex ⇒ B
      has-is-product : is-product π₁ π₂

    open is-product has-is-product public

-- TODO see if it's of any use for instance search
Has-products : Precategory o h → 𝒰 (o ⊔ h)
Has-products C = ∀ x y → Product C x y

module _ {C : Precategory o h} where
  open Cat.Morphism C

  private variable A B : Ob

  ×-unique : (p₁ p₂ : Product C A B) → Product.apex p₁ ≅ Product.apex p₂
  ×-unique p₁ p₂ = iso p₁→p₂ p₂→p₁ p₁→p₂→p₁ p₂→p₁→p₂
    where
      module p₁ = Product p₁
      module p₂ = Product p₂

      p₁→p₂ : p₁.apex ⇒ p₂.apex
      p₁→p₂ = p₂.⟨ p₁.π₁ , p₁.π₂ ⟩ₓ

      p₂→p₁ : p₂.apex ⇒ p₁.apex
      p₂→p₁ = p₁.⟨ p₂.π₁ , p₂.π₂ ⟩ₓ

      p₁→p₂→p₁ : p₁→p₂ ∘ p₂→p₁ ＝ id
      p₁→p₂→p₁ = p₂.unique₂
        (sym (assoc _ _ _) ∙ (_ ◁ p₂.π₁∘⟨⟩) ∙ p₁.π₁∘⟨⟩)
        (sym (assoc _ _ _) ∙ (_ ◁ p₂.π₂∘⟨⟩) ∙ p₁.π₂∘⟨⟩)
        (id-r _) (id-r _)

      p₂→p₁→p₂ : p₂→p₁ ∘ p₁→p₂ ＝ id
      p₂→p₁→p₂ = p₁.unique₂
        (sym (assoc _ _ _) ∙ (_ ◁ p₁.π₁∘⟨⟩) ∙ p₂.π₁∘⟨⟩)
        (sym (assoc _ _ _) ∙ (_ ◁ p₁.π₂∘⟨⟩) ∙ p₂.π₂∘⟨⟩)
        (id-r _) (id-r _)


  module Binary-products (all-products : Has-products C) where
    module products {A} {B} = Product (all-products A B)

    open products renaming (unique to ⟨⟩-unique) public

    instance
      ×-Ob : ×-notation Ob Ob Ob
      ×-Ob .×-notation.Constraint _ _ = ⊤
      ×-Ob ._×_ A B = apex {A} {B}
      {-# OVERLAPPING ×-Ob #-}

      ×-Hom : {A B X Y : Ob} → ×-notation (A ⇒ X) (B ⇒ Y) (A × B ⇒ X × Y)
      ×-Hom .×-notation.Constraint _ _ = ⊤
      ×-Hom ._×_ f g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩ₓ
      {-# OVERLAPPING ×-Hom #-}

    δ : {A : Ob} → A ⇒ A × A
    δ = ⟨ id , id ⟩ₓ

    swap : {A B : Ob} → A × B ⇒ B × A
    swap = ⟨ π₂ , π₁ ⟩ₓ

    ×-assoc : {A B C : Ob} → A × (B × C) ⇒ (A × B) × C
    ×-assoc = ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ₓ , π₂ ∘ π₂ ⟩ₓ
