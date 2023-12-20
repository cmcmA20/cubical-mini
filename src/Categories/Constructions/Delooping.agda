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
  r .Precategory._∘_ = mm._⋆_
  r .id-r = mm.id-r
  r .id-l = mm.id-l
  r .assoc = mm.assoc
