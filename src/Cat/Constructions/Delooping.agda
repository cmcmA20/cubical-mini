{-# OPTIONS --safe #-}
module Cat.Constructions.Delooping where

open import Algebra.Monoid

open import Cat.Prelude

private variable ℓ : Level

-- \MIB
-- Delooping of a monoid
𝑩 : {X : Type ℓ} → Monoid-on X → Precategory 0ℓ ℓ
𝑩 {X} mm = r where
  module mm = Monoid-on mm
  open Precategory

  r : Precategory _ _
  r .Ob = ⊤
  r .Hom _ _ = X
  r .Precategory.id = mm.id
  r .Precategory._∘_ = flip mm._⋆_
  r .id-r = mm.id-l
  r .id-l = mm.id-r
  r .assoc = mm.assoc

module _ {X : Type ℓ} {M : Monoid-on X} where private
  module Mon = Monoid-on M
  module Cat = Precategory (𝑩 M)

  _ :  _∙_ ⦃ Has-binary-op→Trans ⦃ Mon.Has-binary-op-is-n-magma ⦄ ⦄
    ＝ _∙_ ⦃ Cat.Trans-Hom ⦄
  _ = λ _ → Mon._⋆_
