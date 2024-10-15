{-# OPTIONS --safe #-}
module Cat.Gaunt where

import Cat.Morphism
open import Cat.Prelude
open import Cat.Skeletal
open import Cat.Strict

record is-gaunt {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    has-category : is-category C
    has-strict   : is-strict C

  open Univalent.path→equiv has-category
    hiding (hlevel′)
    public
  open IdSS has-category has-strict
    using (K-refl)
    renaming (K to K-iso)
    public

private unquoteDecl is-gaunt-iso = declare-record-iso is-gaunt-iso (quote is-gaunt)

unquoteDecl H-Level-is-gaunt =
  declare-record-hlevel 1 H-Level-is-gaunt (quote is-gaunt)


module _ {o ℓ} {C : Precategory o ℓ} (gaunt : is-gaunt C) where
  open is-gaunt gaunt
  open Cat.Morphism C

  is-gaunt→is-skeletal : is-skeletal C
  is-gaunt→is-skeletal = set-identity-system! $ λ {x y} →
    let instance _ = hlevel-prop-instance (path-is-of-hlevel 1 has-strict x y)
    in rec! (has-category .to-path)

module _ {o ℓ} {C : Precategory o ℓ} where
  skeletal+category→gaunt
    : is-skeletal C
    → is-category C
    → is-gaunt C
  skeletal+category→gaunt _    cat .is-gaunt.has-category = cat
  skeletal+category→gaunt skel _   .is-gaunt.has-strict   = is-skeletal→is-strict _ skel

  skeletal-category≃gaunt
    : is-skeletal C ×ₜ is-category C
    ≃ is-gaunt C
  skeletal-category≃gaunt = prop-extₑ!
      (skeletal+category→gaunt $ₜ²_)
      < is-gaunt→is-skeletal , has-category >
    where open is-gaunt

  open Cat.Morphism C
  skeletal+trivial-automorphisms→gaunt
    : is-skeletal C
    → (∀ {x : Ob} → (f : x ≊ x) → f ＝ refl)
    → is-gaunt C
  skeletal+trivial-automorphisms→gaunt skel trivial-aut =
    skeletal+category→gaunt skel $
      equiv-path→identity-system (≅ₜ→≃ path-equiv)
    where
      open is-gaunt
      open Iso

      path-equiv : {x y : Ob} → (x ≊ y) ≅ (x ＝ y)
      path-equiv .to f = skel .to-path ∣ f ∣₁
      path-equiv .Iso.from = path→equiv
      path-equiv .inverses .Inverses.inv-o = fun-ext λ _ →
        is-skeletal→is-strict _ skel _ _ _ _
      path-equiv {x} .inverses .Inverses.inv-i = fun-ext λ f →
        IdS.J
        skel
        (λ y′ ∥f∥₁ → ∀(f : x ≊ y′) → path→equiv ((skel .to-path ∥f∥₁)) ＝ f)
        (λ f → trivial-aut _ ∙ trivial-aut _ ⁻¹)
        ∣ f ∣₁
        f
