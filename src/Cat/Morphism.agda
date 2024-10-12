{-# OPTIONS --safe --no-exact-split #-}
open import Cat.Base

module Cat.Morphism {o h} (C : Precategory o h) where

open import Meta.Prelude
  hiding (_∘_; id)

open import Meta.Deriving.HLevel
open import Meta.Extensionality
open import Meta.Marker
open import Meta.Record

open import Functions.Embedding
  hiding (_↪_)

open import Cat.Solver

open Precategory C public
private variable
  a b c d : Ob
  f : Hom a b
  n : HLevel

-- Monomorphism (mono)

is-monic : a ⇒ b → Type _
is-monic {a} f = {c : Ob} (g h : c ⇒ a) → f ∘ g ＝ f ∘ h → g ＝ h

record _↪_ (a b : Ob) : Type (o ⊔ h) where
  field
    mor   : a ⇒ b
    monic : is-monic mor

open _↪_ public

unquoteDecl ↪-Iso = declare-record-iso ↪-Iso (quote _↪_)


-- Epimorphism (epi)

is-epic : a ⇒ b → Type _
is-epic {b} f = {c : Ob} (g h : b ⇒ c) → g ∘ f ＝ h ∘ f → g ＝ h

record _↠_ (a b : Ob) : Type (o ⊔ h) where
  field
    mor  : Hom a b
    epic : is-epic mor

open _↠_ public

unquoteDecl ↠-Iso = declare-record-iso ↠-Iso (quote _↠_)

-- The identity morphism is monic and epic.

id-monic : is-monic (id {a})
id-monic g h p = sym (id-l g) ∙∙ p ∙∙ id-l h

id-epic : is-epic (id {a})
id-epic g h p = sym (id-r g) ∙∙ p ∙∙ id-r h


-- Both monos and epis are closed under composition.

monic-∘
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-monic f
  → is-monic g
  → is-monic (f ∘ g)
monic-∘ fm gm a b α = gm _ _ (fm _ _ (sym (assoc _ _ _) ∙∙ α ∙∙ assoc _ _ _))

epic-∘
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-epic f
  → is-epic g
  → is-epic (f ∘ g)
epic-∘ fe ge a b α = fe _ _ (ge _ _ (assoc _ _ _ ∙∙ α ∙∙ sym (assoc _ _ _)))

_∘ₘ_ : b ↪ c → a ↪ b → a ↪ c
(f ∘ₘ g) .mor   = f .mor ∘ g .mor
(f ∘ₘ g) .monic = monic-∘ (f .monic) (g .monic)

_∘ₑ_ : b ↠ c → a ↠ b → a ↠ c
(f ∘ₑ g) .mor = f .mor ∘ g .mor
(f ∘ₑ g) .epic = epic-∘ (f .epic) (g .epic)

instance
  Refl-mono : Refl _↪_
  Refl-mono .refl .mor = id
  Refl-mono .refl .monic = id-monic

  Refl-epi : Refl _↠_
  Refl-epi .refl .mor = id
  Refl-epi .refl .epic = id-epic

  Comp-mono : Comp _↪_ _↪_ _↪_
  Comp-mono ._∙_ f g = g ∘ₘ f

  Comp-epi : Comp _↠_ _↠_ _↠_
  Comp-epi ._∙_ f g = g ∘ₑ f

-- If `f ∘ g` is monic, then `g` must also be monic.

monic-cancel-l
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-monic (f ∘ g)
  → is-monic g
monic-cancel-l {f} fg-monic h h′ p = fg-monic h h′ $
  assoc _ _ _ ∙∙ p ▷ f ∙∙ sym (assoc _ _ _)

-- Dually, if `f ∘ g` is epic, then `f` must also be epic.

epic-cancel-r
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-epic (f ∘ g)
  → is-epic f
epic-cancel-r {g} fg-epic h h' p = fg-epic h h' $
  sym (assoc _ _ _) ∙∙ g ◁ p ∙∙ assoc _ _ _


-- Postcomposition with a mono is an embedding.

monic-postcomp-is-embedding
  : ⦃ _ : H-Level 2 (Hom a c) ⦄ {f : b ⇒ c}
  → is-monic f
  → is-embedding {A = a ⇒ b} (f ∘_)
monic-postcomp-is-embedding monic =
  set-injective→is-embedding (hlevel 2) (monic _ _)

-- Likewise, precomposition with an epi is an embedding.

epic-precomp-embedding
  : ⦃ _ : H-Level 2 (Hom a c) ⦄ {f : a ⇒ b}
  → is-epic f
  → is-embedding {A = b ⇒ c} (_∘ f)
epic-precomp-embedding epic =
  set-injective→is-embedding (hlevel 2) (epic _ _)


-- Sections

id-has-section : has-section (id {a})
id-has-section .section = id
id-has-section .is-section = id-l _

section-of-∘
  : {f : c ⇒ b} {g : b ⇒ c} {h : b ⇒ a} {i : a ⇒ b}
  → f section-of g → h section-of i
  → (h ∘ f) section-of (g ∘ i)
section-of-∘ {f} {g} {h} {i} fg-sect hi-sect =
  (g ∘ i) ∘ h ∘ f  ~⟨ cat! C ⟩
  g ∘ (i ∘ h) ∘ f  ~⟨ (f ◁ hi-sect) ▷ g ⟩
  g ∘ id ∘ f       ~⟨ id-l f ▷ g ⟩
  g ∘ f            ~⟨ fg-sect ⟩
  id               ∎

section-∘
  : {f : b ⇒ c} {g : a ⇒ b}
  → has-section f → has-section g → has-section (f ∘ g)
section-∘ f-sect g-sect .section = g-sect .section ∘ f-sect .section
section-∘ {f} {g} f-sect g-sect .is-section =
  section-of-∘ (f-sect .is-section) (g-sect .is-section)


-- If `f` has a section, then `f` is epic.

has-section→epic
  : {f : Hom a b}
  → has-section f
  → is-epic f
has-section→epic {f} f-sect g h p =
  g                          ~⟨ id-r _ ⟨
  g ∘ id                     ~⟨ f-sect .is-section ▷ g ⟨
  g ∘ f ∘ f-sect .section    ~⟨ assoc _ _ _ ⟨
  (g ∘ f) ∘ f-sect .section  ~⟨ f-sect .section ◁ p ⟩
  (h ∘ f) ∘ f-sect .section  ~⟨ assoc _ _ _ ⟩
  h ∘ (f ∘ f-sect .section)  ~⟨ f-sect .is-section ▷ h ⟩
  h ∘ id                     ~⟨ id-r _ ⟩
  h                          ∎


-- Retractions

id-has-retraction : has-retraction (id {a})
id-has-retraction .retraction = id
id-has-retraction .is-retraction = id-l _

retraction-of-∘
  : {f : c ⇒ b} {g : b ⇒ c} {h : b ⇒ a} {i : a ⇒ b}
  → f retraction-of g → h retraction-of i
  → (h ∘ f) retraction-of (g ∘ i)
retraction-of-∘ = flip section-of-∘

retraction-∘
  : {f : b ⇒ c} {g : a ⇒ b}
  → has-retraction f → has-retraction g
  → has-retraction (f ∘ g)
retraction-∘ f-ret g-ret .retraction = g-ret .retraction ∘ f-ret .retraction
retraction-∘ f-ret g-ret .is-retraction =
  retraction-of-∘ (f-ret .is-retraction) (g-ret .is-retraction)


-- If `f` has a retraction, then `f` is monic.

has-retraction→monic
  : {f : Hom a b}
  → has-retraction f
  → is-monic f
has-retraction→monic {f} f-ret g h p =
  g                            ~⟨ id-l _ ⟨
  id ∘ g                       ~⟨ g ◁ f-ret .is-retraction ⟨
  (f-ret .retraction ∘ f) ∘ g  ~⟨ assoc _ _ _ ⟩
  f-ret .retraction ∘ (f ∘ g)  ~⟨ p ▷ f-ret .retraction ⟩
  f-ret .retraction ∘ f ∘ h    ~⟨ assoc _ _ _ ⟨
  (f-ret .retraction ∘ f) ∘ h  ~⟨ h ◁ f-ret .is-retraction ⟩
  id ∘ h                       ~⟨ id-l _ ⟩
  h                            ∎


-- A section that is also epic is a retract.

section-of+epic→retraction-of
  : {s : b ⇒ a} {r : a ⇒ b}
  → s section-of r
  → is-epic s
  → s retraction-of r
section-of+epic→retraction-of {s} {r} sect epic =
  epic (s ∘ r) id $
    (s ∘ r) ∘ s  ~⟨ assoc s r s ⟩
    s ∘ (r ∘ s)  ~⟨ sect ▷ s ⟩
    s ∘ id       ~⟨ cat! C ⟩
    id ∘ s       ∎


-- Dually, a retraction that is also monic is a section.

retraction-of+monic→section-of
  : {s : b ⇒ a} {r : a ⇒ b}
  → r retraction-of s
  → is-monic r
  → r section-of s
retraction-of+monic→section-of {s = s} {r = r} ret monic =
  monic (s ∘ r) id $
    r ∘ s ∘ r    ~⟨ assoc r s r ⟨
    (r ∘ s) ∘ r  ~⟨ r ◁ ret ⟩
    id ∘ r       ~⟨ cat! C ⟩
    r ∘ id       ∎


has-retraction+epic→has-section
  : {f : Hom a b}
  → has-retraction f
  → is-epic f
  → has-section f
has-retraction+epic→has-section ret epic .section = ret .retraction
has-retraction+epic→has-section ret epic .is-section =
  section-of+epic→retraction-of (ret .is-retraction) epic

has-section+monic→has-retraction
  : {f : Hom a b}
  → has-section f
  → is-monic f
  → has-retraction f
has-section+monic→has-retraction sect monic .retraction = sect .section
has-section+monic→has-retraction sect monic .is-retraction =
  retraction-of+monic→section-of (sect .is-section) monic


-- Isomorphism (iso)

open Inverses

id-qinv : quasi-inverse (id {a})
id-qinv .quasi-inverse.inv = id
id-qinv .quasi-inverse.inverses .inv-o = id-l id
id-qinv .quasi-inverse.inverses .inv-i = id-l id

open Iso

Inverses-∘ : {f : a ⇒ b} {f⁻¹ : b ⇒ a} {g : b ⇒ c} {g⁻¹ : c ⇒ b}
           → Inverses f f⁻¹ → Inverses g g⁻¹ → Inverses (g ∘ f) (f⁻¹ ∘ g⁻¹)
Inverses-∘ {f} {f⁻¹} {g} {g⁻¹} finv ginv = record { inv-o = l ; inv-i = r } where
  module finv = Inverses finv
  module ginv = Inverses ginv

  opaque
    l : (g ∘ f) ∘ f⁻¹ ∘ g⁻¹ ＝ id
    l = (g ∘ f) ∘ f⁻¹ ∘ g⁻¹  ~⟨ cat! C ⟩
        g ∘ (f ∘ f⁻¹) ∘ g⁻¹  ~⟨ (g⁻¹ ◁ finv.inv-o) ▷ g ⟩
        g ∘ id ∘ g⁻¹         ~⟨ cat! C ⟩
        g ∘ g⁻¹              ~⟨ ginv.inv-o ⟩
        id                   ∎

    r : (f⁻¹ ∘ g⁻¹) ∘ g ∘ f ＝ id
    r = (f⁻¹ ∘ g⁻¹) ∘ g ∘ f  ~⟨ cat! C ⟩
        f⁻¹ ∘ (g⁻¹ ∘ g) ∘ f  ~⟨ (f ◁ ginv.inv-i) ▷ f⁻¹ ⟩
        f⁻¹ ∘ id ∘ f         ~⟨ cat! C ⟩
        f⁻¹ ∘ f              ~⟨ finv.inv-i ⟩
        id                   ∎


qinv-∘
  : {f : b ⇒ c} {g : a ⇒ b}
  → quasi-inverse f → quasi-inverse g
  → quasi-inverse (f ∘ g)
qinv-∘ f-inv g-inv = record
  { inv = g-inv.inv ∘ f-inv.inv
  ; inverses = Inverses-∘ g-inv.inverses f-inv.inverses
  }
  where
    module f-inv = quasi-inverse f-inv
    module g-inv = quasi-inverse g-inv

-- _invertible⁻¹
--   : {f : Hom a b}
--   → (f-inv : quasi-inverse f)
--   → quasi-inverse (quasi-inverse.inv f-inv)
-- _invertible⁻¹ {f = f} f-inv .quasi-inverse.inv = f
-- _invertible⁻¹ f-inv .quasi-inverse.inverses .inv-o =
--   quasi-inverse.inv-i f-inv
-- _invertible⁻¹ f-inv .quasi-inverse.inverses .inv-i =
--   quasi-inverse.inv-o f-inv

opaque
  private
    iso-inverse-unique-internal
      : (x y : Ob) (p : x ＝ y) (b d : Ob) (q : b ＝ d) {f : x ≅ b} {g : y ≅ d}
      → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
      → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
    iso-inverse-unique-internal x = J>! λ y → J>! λ {f} {g} d →
      f .from                      ~⟨ f .from .id-r ⟨
      f .from ∘ id                 ~⟨ g .inv-o ▷ f .from ⟨
      f .from ∘ g .to ∘ g .from    ~⟨ assoc _ _ _ ⟨
      (f .from ∘ g .to) ∘ g .from  ~⟨ g .from ◁ (sym d ▷ f .from) ∙ f .inv-i ⟩
      id ∘ g .from                 ~⟨ g .from .id-l ⟩
      g .from                      ∎

  iso-inverse-unique
    : {x y : Ob} (p : x ＝ y) {b d : Ob} (q : b ＝ d) {f : x ≅ b} {g : y ≅ d}
    → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
    → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
  iso-inverse-unique p = iso-inverse-unique-internal _ _ p _ _


module _ ⦃ _ : ∀ {x y} → H-Level 2 (Hom x y) ⦄ where
  private
    inverses-are-prop : {f : a ⇒ b} {g : b ⇒ a} → is-prop (Inverses f g)
    inverses-are-prop = ≅→is-of-hlevel! 1 Inverses-Iso

    ≅-pathᴾ-internal
      : (p : a ＝ c) (q : b ＝ d)
      → {f : a ≅ b} {g : c ≅ d}
      → ＜ f .to   ／ (λ i → Hom (p i) (q i)) ＼ g .to   ＞
      → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
      → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
    ≅-pathᴾ-internal p q r s i .to = r i
    ≅-pathᴾ-internal p q r s i .from = s i
    ≅-pathᴾ-internal p q {f} {g} r s i .inverses =
      is-prop→pathᴾ (λ j → inverses-are-prop {f = r j} {g = s j})
        (f .inverses) (g .inverses) i

  ≅-pathᴾ
    : (p : a ＝ c) (q : b ＝ d) {f : a ≅ b} {g : c ≅ d}
    → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
    → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
  ≅-pathᴾ p q {f} {g} r = ≅-pathᴾ-internal p q r (iso-inverse-unique p q {f = f} {g = g} r)

  ≅-pathᴾ-from
    : (p : a ＝ c) (q : b ＝ d) {f : a ≅ b} {g : c ≅ d}
    → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
    → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
  ≅-pathᴾ-from p q {f} {g} r = ≅-pathᴾ-internal p q (iso-inverse-unique q p {f = f ⁻¹} {g = g ⁻¹} r) r

  ≅-path : {f g : a ≅ b} → f .to ＝ g .to → f ＝ g
  ≅-path = ≅-pathᴾ refl refl

  ≅-path-from : {f g : a ≅ b} → f .from ＝ g .from → f ＝ g
  ≅-path-from = ≅-pathᴾ-from refl refl

  ↪-pathᴾ
    : {a b : I → Ob} {f : a i0 ↪ b i0} {g : a i1 ↪ b i1}
    → ＜ f .mor ／ (λ i → Hom (a i) (b i)) ＼ g .mor ＞
    → ＜ f ／ (λ i → a i ↪ b i) ＼ g ＞
  ↪-pathᴾ {a} {b} {f} {g} pa = go where
    go : ＜ f ／ (λ i → a i ↪ b i) ＼ g ＞
    go i .mor = pa i
    go i .monic {c} = is-prop→pathᴾ
      {B = λ i → (f′ g′ : Hom c (a i)) → pa i ∘ f′ ＝ pa i ∘ g′ → f′ ＝ g′}
      (λ _ → hlevel 1)
      (f .monic) (g .monic) i

  ↠-pathᴾ
    : {a b : I → Ob} {f : a i0 ↠ b i0} {g : a i1 ↠ b i1}
    → ＜ f .mor ／ (λ i → Hom (a i) (b i)) ＼ g .mor ＞
    → ＜ f ／ (λ i → a i ↠ b i) ＼ g ＞
  ↠-pathᴾ {a} {b} {f} {g} pa = go where
    go : ＜ f ／ (λ i → a i ↠ b i) ＼ g ＞
    go i .mor = pa i
    go i .epic {c} = is-prop→pathᴾ
      {B = λ i → (f′ g′ : Hom (b i) c) → f′ ∘ pa i ＝ g′ ∘ pa i → f′ ＝ g′}
      (λ _ → hlevel 1)
      (f .epic) (g .epic) i
