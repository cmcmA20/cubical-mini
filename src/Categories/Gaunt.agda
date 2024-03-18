{-# OPTIONS --safe #-}
module Categories.Gaunt where

open import Structures.IdentitySystem.Interface

import Categories.Morphism
open import Categories.Prelude
open import Categories.Skeletal
open import Categories.Strict

record is-gaunt {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    has-category : is-category C
    has-strict   : is-strict C

  open Univalent.path→iso has-category
    hiding (hlevel′)
    public
  open IdSS has-category has-strict
    using (K-refl)
    renaming (K to K-iso)
    public

private unquoteDecl is-gaunt-iso = declare-record-iso is-gaunt-iso (quote is-gaunt)

is-gaunt-is-prop
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-prop (is-gaunt C)
is-gaunt-is-prop =
  iso→is-of-hlevel 1 is-gaunt-iso hlevel!

instance
  H-Level-is-gaunt
    : ∀ {o ℓ} {C : Precategory o ℓ} {n}
    → H-Level (suc n) (is-gaunt C)
  H-Level-is-gaunt = hlevel-prop-instance is-gaunt-is-prop

module _ {o ℓ} {C : Precategory o ℓ} (gaunt : is-gaunt C) where
  open is-gaunt gaunt
  open Categories.Morphism C

  is-gaunt→is-skeletal : is-skeletal C
  is-gaunt→is-skeletal = set-identity-system hlevel! $
    ∥-∥₁.rec (path-is-of-hlevel′ 1 has-strict _ _) (has-category .to-path)

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

  open Categories.Morphism C
  skeletal+trivial-automorphisms→gaunt
    : is-skeletal C
    → (∀ {x} → (f : x ≅ x) → f ＝ id-iso)
    → is-gaunt C
  skeletal+trivial-automorphisms→gaunt skel trivial-aut =
    skeletal+category→gaunt skel $
      equiv-path→identity-system
        (isoₜ→equiv path-iso)
        (λ _ → transport-refl _)
    where
      open is-gaunt

      path-iso : ∀ {x y} → Iso (x ≅ y) (x ＝ y)
      path-iso .fst f = skel .to-path ∣ f ∣₁
      path-iso .snd .is-iso.inv f = path→iso f
      path-iso .snd .is-iso.rinv _ =
        is-set-β (is-skeletal→is-strict _ skel) _ _ _ _
      path-iso {x} .snd .is-iso.linv f = IdS.J
        skel
        (λ y′ ∥f∥₁ → ∀(f : x ≅ y′) → path→iso ((skel .to-path ∥f∥₁)) ＝ f)
        (λ f → trivial-aut _ ∙ sym (trivial-aut _))
        ∣ f ∣₁
        f
