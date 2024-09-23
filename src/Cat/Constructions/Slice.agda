{-# OPTIONS --safe #-}
open import Cat.Prelude

module Cat.Constructions.Slice {o ℓ} (C : Precategory o ℓ) where
open Precategory C

private variable c : Ob

record /-Obj (c : Ob) : Type (o ⊔ ℓ) where
  constructor cut
  field
    {domain} : Ob
    map      : domain ⇒ c

open /-Obj using (domain)

unquoteDecl /-Obj-iso = declare-record-iso /-Obj-iso (quote /-Obj)

private variable a a′ b b′ x x′ y y′ : /-Obj c

/-Obj-pathᴾ
  : {x y : Ob} {x′ : /-Obj x} {y′ : /-Obj y}
  → (p : x ＝ y)
  → (q : x′ .domain ＝ y′ .domain)
  → ＜ x′ ./-Obj.map ／ (λ i → Hom (q i) (p i)) ＼ y′ ./-Obj.map ＞
  → ＜ x′ ／ (λ i → /-Obj (p i)) ＼ y′ ＞
/-Obj-pathᴾ p q r i .domain = q i
/-Obj-pathᴾ p q r i ./-Obj.map = r i


record /-Hom (a b : /-Obj c) : Type ℓ where
  no-eta-equality
  constructor cut→
  private
    module a = /-Obj a
    module b = /-Obj b
  field
    map      : a.domain ⇒ b.domain
    commutes : b.map ∘ map ＝ a.map

unquoteDecl H-Level-/-Hom =
  declare-record-hlevel 2 H-Level-/-Hom (quote /-Hom)

private variable f g : /-Hom a b

/-Hom-pathᴾ : (p : a ＝ a′) (q : b ＝ b′)
              {f : /-Hom {c} a b} {g : /-Hom a′ b′}
            → ＜ f ./-Hom.map ／ (λ i → Hom (p i .domain) (q i .domain)) ＼ g ./-Hom.map ＞
            → ＜ f ／ (λ i → /-Hom (p i) (q i)) ＼ g ＞
/-Hom-pathᴾ p q {f} {g} r i ./-Hom.map = r i
/-Hom-pathᴾ p q {f} {g} r i ./-Hom.commutes = is-prop→pathᴾ
  (λ j → path-is-of-hlevel 1 (Hom-set (p j .domain) _)
    (q j ./-Obj.map ∘ r j) (p j ./-Obj.map) )
  (f .commutes) (g .commutes) i
  where open /-Hom

instance
  Extensional-/-Hom
    : ∀ {ℓr} ⦃ sa : Extensional (Hom (a .domain) (b .domain)) ℓr ⦄
    → Extensional (/-Hom {c} a b) ℓr
  Extensional-/-Hom ⦃ sa ⦄ = set-injective→extensional!
    (/-Hom-pathᴾ refl refl) sa

Slice : Ob → Precategory _ _
Slice c = go where
  module C = Precategory C
  open /-Hom
  go : Precategory _ _
  go .Ob = /-Obj c
  go .Hom = /-Hom
  go .Hom-set = hlevel!
  go .id .map = C.id
  go .id .commutes = C.id-r _
  go ._∘_ f g .map = f .map C.∘ g .map
  go ._∘_ f g .commutes =
      sym (C.assoc _ _ _)
    ∙ (g .map ◁ f .commutes)
    ∙ g .commutes
  go .id-l _ = ext (C.id-l _)
  go .id-r _ = ext (C.id-r _)
  go .assoc _ _ _ = ext (C.assoc _ _ _)
