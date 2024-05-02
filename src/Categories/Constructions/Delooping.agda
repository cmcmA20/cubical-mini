{-# OPTIONS --safe #-}
module Categories.Constructions.Delooping where

open import Algebra.Monoid

open import Categories.Prelude

-- \MIB
𝑩 : ∀ {ℓ} {M : Type ℓ} → Monoid-on M → Precategory 0ℓ ℓ
𝑩 {M} mm = r where
  module mm = Monoid-on mm
  open Precategory

  r : Precategory _ _
  r .Ob = ⊤
  r .Hom _ _ = M
  r .Hom-set _ _ = hlevel!
  r .Precategory.id = mm.id
  r .Precategory._∘_ = flip mm._⋆_
  r .id-r = mm.id-l
  r .id-l = mm.id-r
  r .assoc _ _ _ = sym (mm.assoc _ _ _)

module _ {ℓ : Level} {X : Type ℓ} {M : Monoid-on X} where private
  module Mon = Monoid-on M
  module Cat = Precategory (𝑩 M)

  _ :  _∙_ ⦃ Transitiveᵘ→Transitive ⦃ Mon.Transitiveᵘ-is-n-magma ⦄ ⦄
    ＝ _∙_ ⦃ Cat.Transitive-Hom ⦄
  _ = λ _ → Mon._⋆_
