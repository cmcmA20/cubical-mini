{-# OPTIONS --safe #-}
module Categories.Constructions.Product where

open import Categories.Prelude

private variable
  o o′ o″ o‴ h h′ h″ h‴ : Level
  C : Precategory o h
  D : Precategory o′ h′
  E : Precategory o″ h″
  B : Precategory o‴ h‴

infixr 8 _×_
_×_ : (C : Precategory o h) (D : Precategory o′ h′) → Precategory _ _
C × D = go where
  module C = Precategory C
  module D = Precategory D
  open Precategory
  go : Precategory _ _
  go .Ob = C.Ob ×ₜ D.Ob
  go .Hom (c , d) (c′ , d′) = C.Hom c c′ ×ₜ D.Hom d d′
  go .Hom-set = hlevel!
  go .id = C.id , D.id
  go ._∘_ (f , g) (f′ , g′) = f C.∘ f′ , g D.∘ g′
  go .id-l (f , g) = ×-path (C.id-l f) (D.id-l g)
  go .id-r (f , g) = ×-path (C.id-r f) (D.id-r g)
  go .assoc (f , g) (f′ , g′) (f″ , g″) =
    ×-path (C.assoc f f′ f″) (D.assoc g g′ g″)

open Functor

Fst : Functor (C × D) C
Fst .F₀ = fst
Fst .F₁ = fst
Fst .F-id = reflₚ
Fst .F-∘ _ _ = reflₚ

Snd : Functor (C × D) D
Snd .F₀ = snd
Snd .F₁ = snd
Snd .F-id = reflₚ
Snd .F-∘ _ _ = reflₚ

Cat⟨_,_⟩ : Functor E C → Functor E D → Functor E (C × D)
Cat⟨ F , G ⟩ .F₀ = < F .F₀ , G .F₀ >
Cat⟨ F , G ⟩ .F₁ = < F .F₁ , G .F₁ >
Cat⟨ F , G ⟩ .F-id = ×-path (F .F-id) (G .F-id)
Cat⟨ F , G ⟩ .F-∘ _ _ = ×-path (F .F-∘ _ _) (G .F-∘ _ _)

_×ᶠ_ : Functor B D → Functor C E → Functor (B × C) (D × E)
(F ×ᶠ G) .F₀ = bimap (F .F₀) (G .F₀)
(F ×ᶠ G) .F₁ = bimap (F .F₁) (G .F₁)
(F ×ᶠ G) .F-id = ×-path (F .F-id) (G .F-id)
(F ×ᶠ G) .F-∘ _ _ = ×-path (F .F-∘ _ _) (G .F-∘ _ _)
