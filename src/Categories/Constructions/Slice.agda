{-# OPTIONS --safe #-}
open import Categories.Prelude

module Categories.Constructions.Slice {o ℓ} (C : Precategory o ℓ) where
open Precategory C

private variable c : Ob

record /-Obj (c : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  constructor cut
  field
    {domain} : Ob
    map      : Hom domain c

open /-Obj using (domain)

unquoteDecl /-Obj-iso = declare-record-iso /-Obj-iso (quote /-Obj)

private variable
  a a′ b b′ x y : /-Obj c

/-Obj-path : (p : x .domain ＝ y .domain)
           → ＜ x ./-Obj.map ／ (λ i → Hom (p i) c) ＼ y ./-Obj.map ＞
           → x ＝ y
/-Obj-path p _ i .domain = p i
/-Obj-path _ q i ./-Obj.map = q i


record /-Hom (a b : /-Obj c) : Type ℓ where
  no-eta-equality
  private
    module a = /-Obj a
    module b = /-Obj b
  field
    map      : Hom a.domain b.domain
    commutes : b.map ∘ map ＝ a.map

private unquoteDecl /-hom-iso = declare-record-iso /-hom-iso (quote /-Hom)

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

Extensional-/-Hom
  : ∀ {ℓr} ⦃ sa : Extensional (Hom (a .domain) (b .domain)) ℓr ⦄
  → Extensional (/-Hom {c} a b) ℓr
Extensional-/-Hom ⦃ sa ⦄ = set-injective→extensional!
  (/-Hom-pathᴾ refl refl) sa

instance
  extensionality-/-hom : Extensionality (/-Hom {c} a b)
  extensionality-/-hom = record { lemma = quote Extensional-/-Hom }

/-Hom-is-set : is-set (/-Hom {c} a b)
/-Hom-is-set = iso→is-of-hlevel 2 /-hom-iso hlevel!

Slice : Ob → Precategory _ _
Slice c = go where
  module C = Precategory C
  open /-Hom
  go : Precategory _ _
  go .Ob = /-Obj c
  go .Hom = /-Hom
  go .Hom-set _ _ = /-Hom-is-set
  go .id .map = C.id
  go .id .commutes = C.id-r _
  go ._∘_ f g .map = f .map C.∘ g .map
  go ._∘_ f g .commutes =
      C.assoc _ _ _
    ∙ ap (C._∘ g .map) (f .commutes)
    ∙ g .commutes
  go .id-l _ = ext (C.id-l _)
  go .id-r _ = ext (C.id-r _)
  go .assoc _ _ _ = ext (C.assoc _ _ _)
