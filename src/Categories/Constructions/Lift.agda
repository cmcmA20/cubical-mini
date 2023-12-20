{-# OPTIONS --safe #-}
module Categories.Constructions.Lift where

open import Categories.Prelude

private variable
  o o′ ℓ ℓ′ : Level

Lift-cat : ∀ o′ ℓ′ → Precategory o ℓ → Precategory (o ⊔ o′) (ℓ ⊔ ℓ′)
Lift-cat o′ ℓ′ C = liftc where
  open Precategory C
  liftc : Precategory _ _
  liftc .Ob = Lift o′ Ob
  liftc .Hom (lift x) (lift y) = Lift ℓ′ (Hom x y)
  liftc .Hom-set = hlevel!
  liftc .id = lift id
  liftc ._∘_ (lift f) (lift g) = lift (f ∘ g)
  liftc .id-r (lift f) = ap lift (id-r f)
  liftc .id-l (lift f) = ap lift (id-l f)
  liftc .assoc (lift f) (lift g) (lift h) = ap lift (assoc f g h)

Lift-functor-l
  : ∀ o″ ℓ″ {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
  → Functor C D
  → Functor (Lift-cat o″ ℓ″ C) D
Lift-functor-l bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ (lift x) = F₀ G x
  F .F₁ (lift f) = F₁ G f
  F .F-id = F-id G
  F .F-∘ (lift f) (lift g) = F-∘ G f g

Lift-functor-r
  : ∀ o″ ℓ″ {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
  → Functor C D
  → Functor C (Lift-cat o″ ℓ″ D)
Lift-functor-r bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ x = lift $ F₀ G x
  F .F₁ f = lift $ F₁ G f
  F .F-id = ap lift $ F-id G
  F .F-∘ f g = ap lift $ F-∘ G f g
