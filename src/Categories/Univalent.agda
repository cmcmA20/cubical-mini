{-# OPTIONS --safe #-}
module Categories.Univalent where

open import Prelude
  hiding (_∘_; id; ≅→=)

open import Categories.Base
open import Categories.Morphism.Instances
import Categories.Morphism as CM

is-category : ∀ {o h} (C : Precategory o h) → Type (o ⊔ h)
is-category C = is-identity-system (CM.Isoᶜ C) (λ _ → refl)
  where open Precategory C

path→iso
  : ∀{o h} {C : Precategory o h} {A B}
  → A ＝ B → CM.Isoᶜ C A B
path→iso {C} {A} p = transport (λ i → CM.Isoᶜ C A (p i)) refl
  where open Precategory C

module _ {o h} {C : Precategory o h} where
  module Univalent′ (r : is-category C) where
    module path→iso = IdS r
      renaming ( to           to iso→path
               ; J            to J-iso
               ; decode-refl  to iso→path-id
               ; η            to iso→path→iso
               ; ε            to path→iso→path
               )

    open CM C public

    open path→iso
      using ( iso→path ; J-iso ; iso→path-id ; iso→path→iso ; path→iso→path )
      public

    Ob-is-groupoid : is-groupoid (C .Precategory.Ob)
    Ob-is-groupoid = path→iso.hlevel′ 2 λ _ _ → hlevel 2


module _ {o h} (C : Precategory o h) where
  open CM C

  private variable
    a b d e : Ob

  open Iso

  Hom-transport : (p : a ＝ d) (q : b ＝ e) (h : Hom a b)
                →  transport (λ i → Hom (p i) (q i)) h
                ＝ path→iso q .to ∘ h ∘ path→iso p .from
  Hom-transport {a} {b} p q h i =
    comp (λ j → Hom (p (i ∨ j)) (q (i ∨ j))) (∂ i) λ where
      j (i = i0) → coe0→i (λ k → Hom (p (j ∧ k)) (q (j ∧ k))) j h
      j (i = i1) → path→iso q .to ∘ h ∘ path→iso p .from
      j (j = i0) → hcomp (∂ i) λ where
        j (i = i0) → id-l (id-r h j) j
        j (i = i1) → q′ i1 ∘ h ∘ p′ i1
        j (j = i0) → q′ i ∘ h ∘ p′ i
    where
      p′ : ＜ id ／ _ ＼ path→iso p .from ＞
      p′ i = coe0→i (λ j → Hom (p (i ∧ j)) a) i id

      q′ : ＜ id ／ _ ＼ path→iso q .to ＞
      q′ i = coe0→i (λ j → Hom b (q (i ∧ j))) i id

  Hom-pathᴾ : {p : a ＝ d} {q : b ＝ e} {h : Hom a b} {h′ : Hom d e}
            → path→iso q .to ∘ h ∘ path→iso p .from ＝ h′
            → ＜ h ／ (λ i → Hom (p i) (q i)) ＼ h′ ＞
  Hom-pathᴾ {p} {q} {h} {h′} prf =
    to-pathᴾ (subst (_＝ h′) (sym (Hom-transport p q h)) prf)

  Hom-transport-id
    : {a b d : Ob} (p : a ＝ b) (q : a ＝ d)
    → transport (λ i → Hom (p i) (q i)) id ＝ path→iso q .to ∘ path→iso p .from
  Hom-transport-id p q = Hom-transport p q _ ∙ ap (path→iso q .to ∘_) (id-l _)

  Hom-transport-refl-l-id
    : (q : a ＝ b)
    → transport (λ i → Hom a (q i)) id ＝ path→iso q .to
  Hom-transport-refl-l-id p =
    Hom-transport-id refl p ∙ ap (path→iso p .to ∘_) (transport-refl _) ∙ id-r _

  Hom-transport-refl-r-id
    : (p : a ＝ b)
    → transport (λ i → Hom (p i) a) id ＝ path→iso p .from
  Hom-transport-refl-r-id p =
    Hom-transport-id p refl ∙ ap (_∘ path→iso p .from) (transport-refl _) ∙ id-l _

  Hom-pathᴾ-refl-l
    : {p : a ＝ d} {h : Hom a b} {h′ : Hom d b}
    → h ∘ path→iso p .from ＝ h′
    → ＜ h ／ (λ i → Hom (p i) b) ＼ h′ ＞
  Hom-pathᴾ-refl-l prf =
    Hom-pathᴾ (ap² _∘_ (transport-refl id) refl ∙∙ id-l _ ∙∙ prf)

  Hom-pathᴾ-refl-r
    : {q : b ＝ d} {h : Hom a b} {h′ : Hom a d}
    → path→iso q .to ∘ h ＝ h′
    → ＜ h ／ (λ i → Hom a (q i)) ＼ h′ ＞
  Hom-pathᴾ-refl-r {q} prf =
    Hom-pathᴾ (ap (path→iso q .to ∘_) (ap² _∘_ refl (transport-refl _))
            ∙∙ ap² _∘_ refl (id-r _)
            ∙∙ prf)


-- TODO more lemmata


module Univalent {o h} {C : Precategory o h} (r : is-category C) where
  open Univalent′ r public

  private variable a b d e : Precategory.Ob C

  open Iso

  Hom-pathᴾ-refl-l-iso
    : {p : a ≅ d} {h : Hom a b} {h′ : Hom d b}
    → h ∘ p .from ＝ h′
    → ＜ h ／ (λ i → Hom (iso→path p i) b) ＼ h′ ＞
  Hom-pathᴾ-refl-l-iso prf =
    Hom-pathᴾ-refl-l C (ap² _∘_ refl (ap from (iso→path→iso _)) ∙ prf)

  Hom-pathᴾ-refl-r-iso
    : {q : b ≅ d} {h : Hom a b} {h′ : Hom a d}
    → q .to ∘ h ＝ h′
    → ＜ h ／ (λ i → Hom a (iso→path q i)) ＼ h′ ＞
  Hom-pathᴾ-refl-r-iso prf =
    Hom-pathᴾ-refl-r C (ap² _∘_ (ap to (iso→path→iso _)) refl ∙ prf)

  Hom-pathᴾ-iso
    : {p : a ≅ d} {q : b ≅ e} {h : Hom a b} {h′ : Hom d e}
    → q .to ∘ h ∘ p .from ＝ h′
    → ＜ h ／ (λ i → Hom (iso→path p i) (iso→path q i)) ＼ h′ ＞
  Hom-pathᴾ-iso {p} {q} {h} {h′} prf =
    Hom-pathᴾ C (ap² _∘_ (ap to (iso→path→iso _))
                (ap² _∘_ refl (ap from (iso→path→iso _)))
              ∙ prf)
