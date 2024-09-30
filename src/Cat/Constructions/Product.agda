{-# OPTIONS --safe #-}
module Cat.Constructions.Product where

open import Cat.Prelude

private variable
  o o′ o″ o‴ h h′ h″ h‴ : Level
  C : Precategory o h
  D : Precategory o′ h′
  E : Precategory o″ h″
  B : Precategory o‴ h‴

_×ᶜ_ : (C : Precategory o h) (D : Precategory o′ h′) → Precategory _ _
C ×ᶜ D = go where
  module C = Precategory C
  module D = Precategory D
  open Precategory
  go : Precategory _ _
  go .Ob = C.Ob × D.Ob
  go .Hom (c , d) (c′ , d′) = (c ⇒ c′) × (d ⇒ d′)
  go .id = C.id , D.id
  go ._∘_ (f , g) (f′ , g′) = f C.∘ f′ , g D.∘ g′
  go .id-l (f , g) = ×-path (C.id-l f) (D.id-l g)
  go .id-r (f , g) = ×-path (C.id-r f) (D.id-r g)
  go .assoc (f , g) (f′ , g′) (f″ , g″) =
    ×-path (C.assoc f f′ f″) (D.assoc g g′ g″)

instance
  ×-Precategory : ×-notation (Precategory o h) (Precategory o′ h′) _
  ×-Precategory .×-notation.Constraint _ _ = ⊤
  ×-Precategory .×-notation._×_ C D = C ×ᶜ D

open Functor

Fst : Functor (C × D) C
Fst .F₀ = fst
Fst .F₁ = fst
Fst .F-id = refl
Fst .F-∘ _ _ = refl

Snd : Functor (C × D) D
Snd .F₀ = snd
Snd .F₁ = snd
Snd .F-id = refl
Snd .F-∘ _ _ = refl

Cat⟨_,_⟩ : E ⇒ C → E ⇒ D → E ⇒ (C × D)
Cat⟨ F , G ⟩ .F₀ = < F .F₀ , G .F₀ >
Cat⟨ F , G ⟩ .F₁ = < F .F₁ , G .F₁ >
Cat⟨ F , G ⟩ .F-id = ×-path (F .F-id) (G .F-id)
Cat⟨ F , G ⟩ .F-∘ _ _ = ×-path (F .F-∘ _ _) (G .F-∘ _ _)

_×ᶠ_ : B ⇒ D → C ⇒ E → (B × C) ⇒ (D × E)
(F ×ᶠ G) .F₀ = bimap (F .F₀) (G .F₀)
(F ×ᶠ G) .F₁ = bimap (F .F₁) (G .F₁)
(F ×ᶠ G) .F-id = ×-path (F .F-id) (G .F-id)
(F ×ᶠ G) .F-∘ _ _ = ×-path (F .F-∘ _ _) (G .F-∘ _ _)

instance
  ×-Functor : ×-notation (B ⇒ D) (C ⇒ E) _
  ×-Functor .×-notation.Constraint _ _ = ⊤
  ×-Functor .×-notation._×_ F G = F ×ᶠ G
