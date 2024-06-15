{-# OPTIONS --safe #-}
module Categories.Constructions.Delooping where

open import Algebra.Monoid

open import Categories.Prelude

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
  r .Hom-set _ _ = hlevel!
  r .Precategory.id = mm.id
  r .Precategory._∘_ = flip mm._⋆_
  r .id-r = mm.id-l
  r .id-l = mm.id-r
  r .assoc _ _ _ = mm.assoc _ _ _ ⁻¹

module _ {X : Type ℓ} {M : Monoid-on X} where private
  module Mon = Monoid-on M
  module Cat = Precategory (𝑩 M)

  _ :  _∙_ ⦃ Transᵘ→Trans ⦃ Mon.Transᵘ-is-n-magma ⦄ ⦄
    ＝ _∙_ ⦃ Cat.Trans-Hom ⦄
  _ = λ _ → Mon._⋆_
