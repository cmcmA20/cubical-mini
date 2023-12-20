{-# OPTIONS --safe #-}
module Categories.Constructions.Product where

open import Categories.Prelude

private variable o o′ h h′ : Level

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
