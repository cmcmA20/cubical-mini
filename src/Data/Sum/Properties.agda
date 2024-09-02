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
  open Iso
  the-iso : _ ≅ _
  the-iso .to = < _∘ inl , _∘ inr >
  the-iso .from (f , g) (inl x) = f x
  the-iso .from (f , g) (inr x) = g x
  the-iso .inverses .Inverses.inv-o = refl
  the-iso .inverses .Inverses.inv-i _ f (inl x) = f (inl x)
  the-iso .inverses .Inverses.inv-i _ f (inr x) = f (inr x)

⊎-ap : A ≃ B → C ≃ D → (A ⊎ C) ≃ (B ⊎ D)
⊎-ap f g = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to = ⊎.dmap (f #_) (g #_)
  from = [ inl ∘ (f ⁻¹ $_) , inr ∘ (g ⁻¹ $_) ]ᵤ
  ri : _
  ri (inl x) = inl # Equiv.ε f x
  ri (inr x) = inr # Equiv.ε g x
  li : _
  li (inl x) = inl # Equiv.η f x
  li (inr x) = inr # Equiv.η g x

⊎-ap-l : A ≃ B → (A ⊎ C) ≃ (B ⊎ C)
⊎-ap-l f = ⊎-ap f refl

⊎-ap-r : B ≃ C → (A ⊎ B) ≃ (A ⊎ C)
⊎-ap-r f = ⊎-ap refl f

⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = ≅→≃ $ iso go go (fun-ext i) (fun-ext i) where
  go : {A : Type ℓᵃ} {B : Type ℓᵇ} → (A ⊎ B) → (B ⊎ A)
  go = [ inr , inl ]ᵤ
  i : {A : Type ℓᵃ} {B : Type ℓᵇ} (x : A ⊎ B) → go (go x) ＝ x
  i (inl _) = refl
  i (inr _) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to = [ [ inl , inr ∘ inl ]ᵤ , inr ∘ inr ]ᵤ
  from = [ inl ∘ inl , [ inl ∘ inr , inr ]ᵤ ]ᵤ
  ri : _
  ri (inl _) = refl
  ri (inr (inl _)) = refl
  ri (inr (inr _)) = refl
  li : _
  li (inl (inl _)) = refl
  li (inl (inr _)) = refl
  li (inr _) = refl

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
  open Iso
  i : _ ≅ _
  i .to (inl x , y) = inl (x , y)
  i .to (inr x , y) = inr (x , y)
  i .from (inl (x , y)) = inl x , y
  i .from (inr (x , y)) = inr x , y
  i .inverses .Inverses.inv-o _ (inl x) = inl x
  i .inverses .Inverses.inv-o _ (inr x) = inr x
  i .inverses .Inverses.inv-i i (inl x , w) = inl x , w
  i .inverses .Inverses.inv-i i (inr x , w) = inr x , w

⊎↪ : A ↪ C → B ↪ D → (A ⊎ B) ↪ (C ⊎ D)
⊎↪ f g .fst = [ inl ∘ f #_ , inr ∘ g #_ ]ᵤ
⊎↪ f g .snd = cancellable→is-embedding λ where
  {inl a} {inl a′} → inl-cancellable ∙ is-embedding→cancellable (f .snd) ∙ inl-cancellable ⁻¹
  {inl a} {inr b}  → ¬→≃⊥ false! ∙ ¬→≃⊥ false! ⁻¹
  {inr b} {inl a}  → ¬→≃⊥ false! ∙ ¬→≃⊥ false! ⁻¹
  {inr b} {inr b′} → inr-cancellable ∙ is-embedding→cancellable (g .snd) ∙ inr-cancellable ⁻¹

⊎-is-of-size : is-of-size ℓᶜ A → is-of-size ℓᵈ B
             → is-of-size (ℓᶜ ⊔ ℓᵈ) (A ⊎ B)
⊎-is-of-size {ℓᶜ} {ℓᵈ} (A , as) (B , bs) = A ⊎ B , ⊎-ap as bs

instance
  Size-⊎ : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
           ⦃ sa : Size ℓᶜ A ⦄
           ⦃ sb : Size ℓᵈ B ⦄
         → Size (ℓᶜ ⊔ ℓᵈ) (A ⊎ B)
  Size-⊎ {ℓᶜ} {ℓᵈ} .Size.has-of-size = ⊎-is-of-size (size ℓᶜ) (size ℓᵈ)
