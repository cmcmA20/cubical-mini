{-# OPTIONS --safe #-}
module Cat.Univalent where

open import Prelude
  hiding (_∘_; id)

open import Cat.Base
open import Cat.Morphism.Instances
import Cat.Morphism as CM

is-category : ∀ {o h} (C : Precategory o h) → Type (o ⊔ h)
is-category C = is-identity-system (λ (x y : Ob) → x ≊ y) (λ _ → refl)
  where open Precategory C

module _ {o h} {C : Precategory o h} where
  open Precategory C
  path→equiv : {A B : Ob} → A ＝ B → A ≊ B
  path→equiv {A} p = transport (λ i → A ≊ p i) refl

module _ {o h} {C : Precategory o h} where
  module Univalent′ (r : is-category C) where
    module path→equiv = IdS r
      renaming ( to           to equiv→path
               ; J            to J-equiv
               ; decode-refl  to equiv→path-id
               ; η            to equiv→path→equiv
               ; ε            to path→equiv→path
               )

    open CM C public

    open path→equiv
      using ( equiv→path ; J-equiv ; equiv→path-id ; equiv→path→equiv ; path→equiv→path )
      public

    instance
      H-Level-Ob-univalent : ∀ {n} ⦃ _ : n ≥ʰ 1 ⦄ ⦃ hl : ∀ {x y} → H-Level n (Hom x y) ⦄ → H-Level (suc n) (C .Precategory.Ob)
      H-Level-Ob-univalent {n = suc m} ⦃ s≤ʰs _ ⦄ .H-Level.has-of-hlevel =
        path→equiv.hlevel′ (1 + m) λ _ _ → ≅→is-of-hlevel! (1 + m) Biinv-Iso
      {-# INCOHERENT H-Level-Ob-univalent #-}


module _ {o h} (C : Precategory o h) where
  open CM C

  private variable a b d e : Ob

  open Biinv

  Hom-transport : (p : a ＝ d) (q : b ＝ e) (h : Hom a b)
                →  transport (λ i → Hom (p i) (q i)) h
                ＝ path→equiv q .to ∘ h ∘ path→equiv p .from
  Hom-transport {a} {b} p q h i =
    comp (λ j → Hom (p (i ∨ j)) (q (i ∨ j))) (∂ i) λ where
      j (i = i0) → coe0→i (λ k → Hom (p (j ∧ k)) (q (j ∧ k))) j h
      j (i = i1) → path→equiv q .to ∘ h ∘ path→equiv p .from
      j (j = i0) → hcomp (∂ i) λ where
        j (i = i0) → id-l (id-r h j) j
        j (i = i1) → q′ i1 ∘ h ∘ p′ i1
        j (j = i0) → q′ i ∘ h ∘ p′ i
    where
      p′ : ＜ id ／ _ ＼ path→equiv p .from ＞
      p′ i = coe0→i (λ j → Hom (p (i ∧ j)) a) i id

      q′ : ＜ id ／ _ ＼ path→equiv q .to ＞
      q′ i = coe0→i (λ j → Hom b (q (i ∧ j))) i id

  Hom-pathᴾ : {p : a ＝ d} {q : b ＝ e} {h : Hom a b} {h′ : Hom d e}
            → path→equiv q .to ∘ h ∘ path→equiv p .from ＝ h′
            → ＜ h ／ (λ i → Hom (p i) (q i)) ＼ h′ ＞
  Hom-pathᴾ {p} {q} {h} {h′} prf =
    to-pathᴾ (subst (_＝ h′) (sym (Hom-transport p q h)) prf)

  Hom-transport-id
    : {a b d : Ob} (p : a ＝ b) (q : a ＝ d)
    → transport (λ i → Hom (p i) (q i)) id ＝ path→equiv q .to ∘ path→equiv p .from
  Hom-transport-id p q = Hom-transport p q _ ∙ (id-l _ ▷ path→equiv q .to)

  Hom-transport-refl-l-id
    : (q : a ＝ b)
    → transport (λ i → Hom a (q i)) id ＝ path→equiv q .to
  Hom-transport-refl-l-id p =
    Hom-transport-id refl p ∙ (transport-refl _ ▷ path→equiv p .to) ∙ id-r _

  Hom-transport-refl-r-id
    : (p : a ＝ b)
    → transport (λ i → Hom (p i) a) id ＝ path→equiv p .from
  Hom-transport-refl-r-id p =
    Hom-transport-id p refl ∙ (path→equiv p .from ◁ transport-refl _) ∙ id-l _

  Hom-pathᴾ-refl-l
    : {p : a ＝ d} {h : Hom a b} {h′ : Hom d b}
    → h ∘ path→equiv p .from ＝ h′
    → ＜ h ／ (λ i → Hom (p i) b) ＼ h′ ＞
  Hom-pathᴾ-refl-l prf =
    Hom-pathᴾ (ap² _∘_ (transport-refl id) refl ∙∙ id-l _ ∙∙ prf)

  Hom-pathᴾ-refl-r
    : {q : b ＝ d} {h : Hom a b} {h′ : Hom a d}
    → path→equiv q .to ∘ h ＝ h′
    → ＜ h ／ (λ i → Hom a (q i)) ＼ h′ ＞
  Hom-pathᴾ-refl-r {q} prf =
    Hom-pathᴾ (ap (path→equiv q .to ∘_) (ap² _∘_ refl (transport-refl _))
            ∙∙ ap² _∘_ refl (id-r _)
            ∙∙ prf)


-- TODO more lemmata


module Univalent {o h} {C : Precategory o h} (r : is-category C) where
  open Univalent′ r public

  private variable a b d e : Precategory.Ob C

  open Biinv

  Hom-pathᴾ-refl-l-equiv
    : {p : a ≊ d} {h : Hom a b} {h′ : Hom d b}
    → h ∘ p .from ＝ h′
    → ＜ h ／ (λ i → Hom (equiv→path p i) b) ＼ h′ ＞
  Hom-pathᴾ-refl-l-equiv prf =
    Hom-pathᴾ-refl-l C (ap² _∘_ refl (ap from (equiv→path→equiv # _ ⁻¹)) ∙ prf)

  Hom-pathᴾ-refl-r-equiv
    : {q : b ≊ d} {h : Hom a b} {h′ : Hom a d}
    → q .to ∘ h ＝ h′
    → ＜ h ／ (λ i → Hom a (equiv→path q i)) ＼ h′ ＞
  Hom-pathᴾ-refl-r-equiv prf =
    Hom-pathᴾ-refl-r C (ap² _∘_ (ap to (equiv→path→equiv # _ ⁻¹)) refl ∙ prf)

  Hom-pathᴾ-equiv
    : {p : a ≊ d} {q : b ≊ e} {h : Hom a b} {h′ : Hom d e}
    → q .to ∘ h ∘ p .from ＝ h′
    → ＜ h ／ (λ i → Hom (equiv→path p i) (equiv→path q i)) ＼ h′ ＞
  Hom-pathᴾ-equiv {p} {q} {h} {h′} prf =
    Hom-pathᴾ C (ap² _∘_ (ap to (equiv→path→equiv # _ ⁻¹))
                (ap² _∘_ refl (ap from (equiv→path→equiv # _ ⁻¹)))
              ∙ prf)
