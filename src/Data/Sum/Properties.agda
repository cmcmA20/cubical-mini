{-# OPTIONS --safe #-}
module Data.Sum.Properties where

open import Meta.Prelude

open import Functions.Embedding

open import Data.Empty.Base
open import Data.Empty.Properties
  using (¬→≃⊥)
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base as ⊎
open import Data.Sum.Path

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

universal : {A : Type ℓᵃ} {B : Type ℓᵇ}
            {C : A ⊎ B → Type ℓᶜ}
          → (Π[ x ꞉ A ⊎ B ] C x)
          ≃ ( (Π[ x ꞉ A ] C (inl x))
            × (Π[ y ꞉ B ] C (inr y))
            )
universal = ≅→≃ the-iso where
  the-iso : Iso _ _
  the-iso .fst f = (λ x → f (inl x)) , (λ x → f (inr x))
  the-iso .snd .is-iso.inv (f , g) (inl x) = f x
  the-iso .snd .is-iso.inv (f , g) (inr x) = g x
  the-iso .snd .is-iso.rinv x = refl
  the-iso .snd .is-iso.linv f i (inl x) = f (inl x)
  the-iso .snd .is-iso.linv f i (inr x) = f (inr x)

⊎-ap : A ≃ B → C ≃ D → (A ⊎ C) ≃ (B ⊎ D)
⊎-ap (f , f-eqv) (g , g-eqv) = ≅→≃ cong′ where
  f-iso = is-equiv→is-iso f-eqv
  g-iso = is-equiv→is-iso g-eqv

  cong′ : Iso _ _
  cong′ .fst = ⊎.dmap f g
  cong′ .snd .is-iso.inv  (inl x) = inl (f-iso .is-iso.inv x)
  cong′ .snd .is-iso.inv  (inr x) = inr (g-iso .is-iso.inv x)
  cong′ .snd .is-iso.rinv (inl x) = ap inl (f-iso .is-iso.rinv x)
  cong′ .snd .is-iso.rinv (inr x) = ap inr (g-iso .is-iso.rinv x)
  cong′ .snd .is-iso.linv (inl x) = ap inl (f-iso .is-iso.linv x)
  cong′ .snd .is-iso.linv (inr x) = ap inr (g-iso .is-iso.linv x)

⊎-ap-l : A ≃ B → (A ⊎ C) ≃ (B ⊎ C)
⊎-ap-l f = ⊎-ap f refl

⊎-ap-r : B ≃ C → (A ⊎ B) ≃ (A ⊎ C)
⊎-ap-r f = ⊎-ap refl f

⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = ≅→≃ i where
  i : Iso _ _
  i .fst (inl x) = inr x
  i .fst (inr x) = inl x

  i .snd .is-iso.inv (inl x) = inr x
  i .snd .is-iso.inv (inr x) = inl x

  i .snd .is-iso.rinv (inl x) = refl
  i .snd .is-iso.rinv (inr x) = refl
  i .snd .is-iso.linv (inl x) = refl
  i .snd .is-iso.linv (inr x) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = ≅→≃ i where
  i : Iso _ _
  i .fst (inl (inl x)) = inl x
  i .fst (inl (inr x)) = inr (inl x)
  i .fst (inr x)       = inr (inr x)

  i .snd .is-iso.inv (inl x)       = inl (inl x)
  i .snd .is-iso.inv (inr (inl x)) = inl (inr x)
  i .snd .is-iso.inv (inr (inr x)) = inr x

  i .snd .is-iso.rinv (inl x) = refl
  i .snd .is-iso.rinv (inr (inl x)) = refl
  i .snd .is-iso.rinv (inr (inr x)) = refl

  i .snd .is-iso.linv (inl (inl x)) = refl
  i .snd .is-iso.linv (inl (inr x)) = refl
  i .snd .is-iso.linv (inr x) = refl

⊎-zero-r : (A ⊎ ⊥) ≃ A
⊎-zero-r .fst (inl x) = x
⊎-zero-r .snd .equiv-proof y .fst = inl y , refl
⊎-zero-r .snd .equiv-proof y .snd (inl x , p) i = inl (p (~ i)) , λ j → p (~ i ∨ j)

⊎-zero-l : (⊥ ⊎ A) ≃ A
⊎-zero-l .fst (inr x) = x
⊎-zero-l .snd .equiv-proof y .fst = inr y , refl
⊎-zero-l .snd .equiv-proof y .snd (inr x , p) i = inr (p (~ i)) , λ j → p (~ i ∨ j)

⊎-×-distribute : ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
⊎-×-distribute = ≅→≃ i where
  i : Iso _ _
  i .fst (inl x , y) = inl (x , y)
  i .fst (inr x , y) = inr (x , y)
  i .snd .is-iso.inv (inl (x , y)) = inl x , y
  i .snd .is-iso.inv (inr (x , y)) = inr x , y
  i .snd .is-iso.rinv (inl x) = refl
  i .snd .is-iso.rinv (inr x) = refl
  i .snd .is-iso.linv (inl x , _) = refl
  i .snd .is-iso.linv (inr x , _) = refl

⊎↪ : A ↪ C → B ↪ D → (A ⊎ B) ↪ (C ⊎ D)
⊎↪ f g .fst = [ inl ∘ f #_ , inr ∘ g #_ ]ᵤ
⊎↪ f g .snd = cancellable→is-embedding λ where
  {inl a} {inl a′} → inl-cancellable ∙ is-embedding→cancellable (f .snd) ∙ inl-cancellable ⁻¹
  {inl a} {inr b}  → ¬→≃⊥ false! ∙ ¬→≃⊥ false! ⁻¹
  {inr b} {inl a}  → ¬→≃⊥ false! ∙ ¬→≃⊥ false! ⁻¹
  {inr b} {inr b′} → inr-cancellable ∙ is-embedding→cancellable (g .snd) ∙ inr-cancellable ⁻¹

⊎-is-of-size : is-of-size ℓᶜ A → is-of-size ℓᵈ B
             → is-of-size (ℓᶜ ⊔ ℓᵈ) (A ⊎ B)
⊎-is-of-size {ℓᶜ} {ℓᵈ} Asz Bsz =
  Asz .fst ⊎ Bsz .fst , ⊎-ap (Asz .snd) (Bsz .snd)

instance
  Size-⊎ : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
           ⦃ sa : Size ℓᶜ A ⦄
           ⦃ sb : Size ℓᵈ B ⦄
         → Size (ℓᶜ ⊔ ℓᵈ) (A ⊎ B)
  Size-⊎ {ℓᶜ} {ℓᵈ} .Size.has-of-size = ⊎-is-of-size (size ℓᶜ) (size ℓᵈ)
  {-# OVERLAPPABLE Size-⊎ #-}
