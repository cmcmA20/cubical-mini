{-# OPTIONS --safe #-}
open import Categories.Base

module Categories.Morphism {o h} (C : Precategory o h) where

open import Meta.Prelude
  hiding (_∘_; _≅_; id; section)

open import Meta.Deriving.HLevel
open import Meta.Extensionality
open import Meta.Marker
open import Meta.Record

open import Functions.Embedding
  hiding (_↪_)

open import Categories.Solver

open import Data.Nat.Order.Inductive

open Precategory C public
private variable
  a b c d : Ob
  f : Hom a b
  n : HLevel

-- Monomorphism (mono)

is-monic : Hom a b → Type _
is-monic {a} f = ∀ {c} → (g h : Hom c a) → f ∘ g ＝ f ∘ h → g ＝ h

record _↪_ (a b : Ob) : Type (o ⊔ h) where
  field
    mor   : Hom a b
    monic : is-monic mor

open _↪_ public


-- Epimorphism (epi)

is-epic : Hom a b → Type _
is-epic {b} f = ∀ {c} → (g h : Hom b c) → g ∘ f ＝ h ∘ f → g ＝ h

record _↠_ (a b : Ob) : Type (o ⊔ h) where
  field
    mor  : Hom a b
    epic : is-epic mor

open _↠_ public


-- The identity morphism is monic and epic.

id-monic : is-monic (id {a})
id-monic g h p = sym (id-l g) ∙∙ p ∙∙ id-l h

id-epic : is-epic (id {a})
id-epic g h p = sym (id-r g) ∙∙ p ∙∙ id-r h


-- Both monos and epis are closed under composition.

monic-∘
  : {f : Hom b c} {g : Hom a b}
  → is-monic f
  → is-monic g
  → is-monic (f ∘ g)
monic-∘ fm gm a b α = gm _ _ (fm _ _ (assoc _ _ _ ∙∙ α ∙∙ sym (assoc _ _ _)))

epic-∘
  : {f : Hom b c} {g : Hom a b}
  → is-epic f
  → is-epic g
  → is-epic (f ∘ g)
epic-∘ fe ge a b α = fe _ _ (ge _ _ (sym (assoc _ _ _) ∙∙ α ∙∙ (assoc _ _ _)))

_∘ₘ_ : b ↪ c → a ↪ b → a ↪ c
(f ∘ₘ g) .mor   = f .mor ∘ g .mor
(f ∘ₘ g) .monic = monic-∘ (f .monic) (g .monic)

_∘ₑ_ : b ↠ c → a ↠ b → a ↠ c
(f ∘ₑ g) .mor = f .mor ∘ g .mor
(f ∘ₑ g) .epic = epic-∘ (f .epic) (g .epic)


-- If `f ∘ g` is monic, then `g` must also be monic.

monic-cancel-l
  : {f : Hom b c} {g : Hom a b}
  → is-monic (f ∘ g)
  → is-monic g
monic-cancel-l {f} fg-monic h h′ p = fg-monic h h′ $
  sym (assoc _ _ _) ∙∙ ap (f ∘_) p ∙∙ assoc _ _ _

-- Dually, if `f ∘ g` is epic, then `f` must also be epic.

epic-cancel-r
  : {f : Hom b c} {g : Hom a b}
  → is-epic (f ∘ g)
  → is-epic f
epic-cancel-r {g} fg-epic h h' p = fg-epic h h' $
  assoc _ _ _ ∙∙ ap (_∘ g) p ∙∙ sym (assoc _ _ _)


-- Postcomposition with a mono is an embedding.

monic-postcomp-is-embedding
  : {f : Hom b c}
  → is-monic f
  → is-embedding {A = Hom a b} (f ∘_)
monic-postcomp-is-embedding monic =
  set-injective→is-embedding (Hom-set _ _) (monic _ _)

-- Likewise, precomposition with an epi is an embedding.

epic-precomp-embedding
  : {f : Hom a b}
  → is-epic f
  → is-embedding {A = Hom b c} (_∘ f)
epic-precomp-embedding epic =
  set-injective→is-embedding (Hom-set _ _) (epic _ _)


-- Sections

_section-of_ : (s : Hom b a) (r : Hom a b) → Type _
s section-of r = r ∘ s ＝ id

record has-section (r : Hom a b) : Type h where
  constructor make-section
  field
    section    : Hom b a
    is-section : section section-of r

open has-section public

id-has-section : has-section (id {a})
id-has-section .section = id
id-has-section .is-section = id-l _

section-of-∘
  : {f : Hom c b} {g : Hom b c} {h : Hom b a} {i : Hom a b}
  → f section-of g → h section-of i
  → (h ∘ f) section-of (g ∘ i)
section-of-∘ {f} {g} {h} {i} fg-sect hi-sect =
  (g ∘ i) ∘ h ∘ f    ＝⟨ cat! C ⟩
  g ∘ ⌜ i ∘ h ⌝ ∘ f  ＝⟨ ap! (hi-sect) ⟩
  g ∘ ⌜ id ∘ f ⌝     ＝⟨ ap! (id-l _) ⟩
  g ∘ f              ＝⟨ fg-sect ⟩
  id                 ∎

section-∘
  : {f : Hom b c} {g : Hom a b}
  → has-section f → has-section g → has-section (f ∘ g)
section-∘ f-sect g-sect .section = g-sect .section ∘ f-sect .section
section-∘ {f} {g} f-sect g-sect .is-section =
  section-of-∘ (f-sect .is-section) (g-sect .is-section)


-- If `f` has a section, then `f` is epic.

has-section→epic
  : has-section f
  → is-epic f
has-section→epic {f = f} f-sect g h p =
  g                            ＝˘⟨ id-r _ ⟩
  g ∘ ⌜ id ⌝                   ＝˘⟨ ap¡ (f-sect .is-section) ⟩
  g ∘ f ∘ f-sect .section      ＝⟨ assoc _ _ _ ⟩
  ⌜ g ∘ f ⌝ ∘ f-sect .section  ＝⟨ ap! p ⟩
  (h ∘ f) ∘ f-sect .section    ＝˘⟨ assoc _ _ _ ⟩
  h ∘ ⌜ f ∘ f-sect .section ⌝  ＝⟨ ap! (f-sect .is-section) ⟩
  h ∘ id                       ＝⟨ id-r _ ⟩
  h                            ∎


-- Retracts


_retract-of_ : (r : Hom a b) (s : Hom b a) → Type _
r retract-of s = r ∘ s ＝ id

record has-retract (s : Hom b a) : Type h where
  constructor make-retract
  field
    retract : Hom a b
    is-retract : retract retract-of s

open has-retract public

id-has-retract : has-retract (id {a})
id-has-retract .retract = id
id-has-retract .is-retract = id-l _

retract-of-∘
  : {f : Hom c b} {g : Hom b c} {h : Hom b a} {i : Hom a b}
  → f retract-of g → h retract-of i
  → (h ∘ f) retract-of (g ∘ i)
retract-of-∘ = flip section-of-∘

retract-∘
  : {f : Hom b c} {g : Hom a b}
  → has-retract f → has-retract g
  → has-retract (f ∘ g)
retract-∘ f-ret g-ret .retract = g-ret .retract ∘ f-ret .retract
retract-∘ f-ret g-ret .is-retract =
  retract-of-∘ (f-ret .is-retract) (g-ret .is-retract)


-- If `f` has a retract, then `f` is monic.

has-retract→monic
  : has-retract f
  → is-monic f
has-retract→monic {f} f-ret g h p =
  g                           ＝˘⟨ id-l _ ⟩
  ⌜ id ⌝ ∘ g                  ＝˘⟨ ap¡ (f-ret .is-retract) ⟩
  (f-ret .retract ∘ f) ∘ g    ＝˘⟨ assoc _ _ _ ⟩
  f-ret .retract ∘ ⌜ f ∘ g ⌝  ＝⟨ ap! p ⟩
  f-ret .retract ∘ f ∘ h      ＝⟨ assoc _ _ _ ⟩
  ⌜ f-ret .retract ∘ f ⌝ ∘ h  ＝⟨ ap! (f-ret .is-retract) ⟩
  id ∘ h                      ＝⟨ id-l _ ⟩
  h                           ∎


-- A section that is also epic is a retract.

section-of+epic→retract-of
  : {s : Hom b a} {r : Hom a b}
  → s section-of r
  → is-epic s
  → s retract-of r
section-of+epic→retract-of {s} {r} sect epic =
  epic (s ∘ r) id $
    (s ∘ r) ∘ s    ＝˘⟨ assoc s r s ⟩
    s ∘ ⌜ r ∘ s ⌝  ＝⟨ ap! sect ⟩
    s ∘ id         ＝⟨ cat! C ⟩
    id ∘ s         ∎


-- Dually, a retract that is also monic is a section.

retract-of+monic→section-of
  : {s : Hom b a} {r : Hom a b}
  → r retract-of s
  → is-monic r
  → r section-of s
retract-of+monic→section-of {s = s} {r = r} ret monic =
  monic (s ∘ r) id $
    r ∘ s ∘ r      ＝⟨ assoc r s r ⟩
    ⌜ r ∘ s ⌝ ∘ r  ＝⟨ ap! ret ⟩
    id ∘ r         ＝⟨ cat! C ⟩
    r ∘ id         ∎


has-retract+epic→has-section
  : has-retract f
  → is-epic f
  → has-section f
has-retract+epic→has-section ret epic .section = ret .retract
has-retract+epic→has-section ret epic .is-section =
  section-of+epic→retract-of (ret .is-retract) epic

has-section+monic→has-retract
  : has-section f
  → is-monic f
  → has-retract f
has-section+monic→has-retract sect monic .retract = sect .section
has-section+monic→has-retract sect monic .is-retract =
  retract-of+monic→section-of (sect .is-section) monic


-- Isomorphism (iso)

record Inverses (f : Hom a b) (g : Hom b a) : Type h where
  constructor make-inverses
  field
    inv-l : f ∘ g ＝ id
    inv-r : g ∘ f ＝ id

open Inverses

private
  unquoteDecl H-Level-inverses =
    declare-record-hlevel 1 H-Level-inverses (quote Inverses)

inverses-are-prop : {f : Hom a b} {g : Hom b a} → is-prop (Inverses f g)
inverses-are-prop = hlevel 1


record is-invertible (f : Hom a b) : Type h where
  field
    inv : Hom b a
    inverses : Inverses f inv

  open Inverses inverses public

  op : is-invertible _
  op .inv = f
  op .inverses .inv-l = inv-r inverses
  op .inverses .inv-r = inv-l inverses

opaque
  is-invertible-is-prop : {f : Hom a b} → is-prop (is-invertible f)
  is-invertible-is-prop {a} {b} {f} g h = p where
    module g = is-invertible g
    module h = is-invertible h

    g≡h : g.inv ＝ h.inv
    g≡h =
      g.inv             ＝⟨ sym (id-r _) ∙ ap² _∘_ refl (sym h.inv-l) ⟩
      g.inv ∘ f ∘ h.inv ＝⟨ assoc _ _ _ ∙∙ ap² _∘_ g.inv-r refl ∙∙ id-l _ ⟩
      h.inv             ∎

    p : g ＝ h
    p i .is-invertible.inv = g≡h i
    p i .is-invertible.inverses =
     is-prop→pathᴾ (λ i → inverses-are-prop {g = g≡h i}) g.inverses h.inverses i

id-invertible : is-invertible (id {a})
id-invertible .is-invertible.inv = id
id-invertible .is-invertible.inverses .inv-l = id-l id
id-invertible .is-invertible.inverses .inv-r = id-l id


record _≅_ (a b : Ob) : Type h where
  field
    to       : Hom a b
    from     : Hom b a
    inverses : Inverses to from

  open Inverses inverses public

open _≅_ public

id-iso : a ≅ a
id-iso .to = id
id-iso .from = id
id-iso .inverses .inv-l = id-l id
id-iso .inverses .inv-r = id-l id

Isomorphism = _≅_

Inverses-∘ : {f : Hom a b} {f⁻¹ : Hom b a} {g : Hom b c} {g⁻¹ : Hom c b}
           → Inverses f f⁻¹ → Inverses g g⁻¹ → Inverses (g ∘ f) (f⁻¹ ∘ g⁻¹)
Inverses-∘ {f} {f⁻¹} {g} {g⁻¹} finv ginv = record { inv-l = l ; inv-r = r } where
  module finv = Inverses finv
  module ginv = Inverses ginv

  opaque
    l : (g ∘ f) ∘ f⁻¹ ∘ g⁻¹ ＝ id
    l = (g ∘ f) ∘ f⁻¹ ∘ g⁻¹    ＝⟨ cat! C ⟩
        g ∘ ⌜ f ∘ f⁻¹ ⌝ ∘ g⁻¹  ＝⟨ ap! finv.inv-l ⟩
        g ∘ id ∘ g⁻¹           ＝⟨ cat! C ⟩
        g ∘ g⁻¹                ＝⟨ ginv.inv-l ⟩
        id                     ∎

    r : (f⁻¹ ∘ g⁻¹) ∘ g ∘ f ＝ id
    r = (f⁻¹ ∘ g⁻¹) ∘ g ∘ f    ＝⟨ cat! C ⟩
        f⁻¹ ∘ ⌜ g⁻¹ ∘ g ⌝ ∘ f  ＝⟨ ap! ginv.inv-r ⟩
        f⁻¹ ∘ id ∘ f           ＝⟨ cat! C ⟩
        f⁻¹ ∘ f                ＝⟨ finv.inv-r ⟩
        id                     ∎

_∘ᵢ_ : a ≅ b → b ≅ c → a ≅ c
(f ∘ᵢ g) .to = g .to ∘ f .to
(f ∘ᵢ g) .from = f .from ∘ g .from
(f ∘ᵢ g) .inverses = Inverses-∘ (f .inverses) (g .inverses)

infixr 40 _∘ᵢ_

invertible-∘
  : {f : Hom b c} {g : Hom a b}
  → is-invertible f → is-invertible g
  → is-invertible (f ∘ g)
invertible-∘ f-inv g-inv = record
  { inv = g-inv.inv ∘ f-inv.inv
  ; inverses = Inverses-∘ g-inv.inverses f-inv.inverses
  }
  where
    module f-inv = is-invertible f-inv
    module g-inv = is-invertible g-inv

_invertible⁻¹
  : (f-inv : is-invertible f)
  → is-invertible (is-invertible.inv f-inv)
_invertible⁻¹ {f = f} f-inv .is-invertible.inv = f
_invertible⁻¹ f-inv .is-invertible.inverses .inv-l =
  is-invertible.inv-r f-inv
_invertible⁻¹ f-inv .is-invertible.inverses .inv-r =
  is-invertible.inv-l f-inv

_ᵢ⁻¹ : a ≅ b → b ≅ a
(f ᵢ⁻¹) .to = f .from
(f ᵢ⁻¹) .from = f .to
(f ᵢ⁻¹) .inverses .inv-l = f .inverses .inv-r
(f ᵢ⁻¹) .inverses .inv-r = f .inverses .inv-l

make-invertible : {f : Hom a b} (g : Hom b a) → f ∘ g ＝ id → g ∘ f ＝ id → is-invertible f
make-invertible g _ _ .is-invertible.inv = g
make-invertible _ p _ .is-invertible.inverses .inv-l = p
make-invertible _ _ q .is-invertible.inverses .inv-r = q

make-iso : (f : Hom a b) (g : Hom b a) → f ∘ g ＝ id → g ∘ f ＝ id → a ≅ b
make-iso f _ _ _ ._≅_.to = f
make-iso _ g _ _ ._≅_.from = g
make-iso _ _ p _ ._≅_.inverses .inv-l = p
make-iso _ _ _ q ._≅_.inverses .inv-r = q

inverses→invertible : {f : Hom a b} {g : Hom b a} → Inverses f g → is-invertible f
inverses→invertible x .is-invertible.inv = _
inverses→invertible x .is-invertible.inverses = x

invertible→iso : (f : Hom a b) → is-invertible f → a ≅ b
invertible→iso f _ .to = f
invertible→iso _ x .from = x .is-invertible.inv
invertible→iso _ x .inverses = x .is-invertible.inverses

is-invertible-inverse
  : {f : Hom a b} (g : is-invertible f) → is-invertible (g .is-invertible.inv)
is-invertible-inverse g = make-invertible _ (inv-r g) (inv-l g) where
  open Inverses (g .is-invertible.inverses)

iso→invertible : (i : a ≅ b) → is-invertible (i ._≅_.to)
iso→invertible i .is-invertible.inv = i ._≅_.from
iso→invertible i .is-invertible.inverses = i ._≅_.inverses

private
  ≅-pathᴾ-internal
    : (p : a ＝ c) (q : b ＝ d)
    → {f : a ≅ b} {g : c ≅ d}
    → ＜ f ._≅_.to   ／ (λ i → Hom (p i) (q i)) ＼ g ._≅_.to   ＞
    → ＜ f ._≅_.from ／ (λ i → Hom (q i) (p i)) ＼ g ._≅_.from ＞
    → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
  ≅-pathᴾ-internal p q r s i .to = r i
  ≅-pathᴾ-internal p q r s i .from = s i
  ≅-pathᴾ-internal p q {f} {g} r s i .inverses =
    is-prop→pathᴾ (λ j → inverses-are-prop {f = r j} {g = s j})
      (f .inverses) (g .inverses) i

opaque
  private
    inverse-unique-internal
      : (x y : Ob) (p : x ＝ y) (b d : Ob) (q : b ＝ d) {f : x ≅ b} {g : y ≅ d}
      → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
      → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
    inverse-unique-internal x = Jₚ> λ y → Jₚ> λ {f} {g} d →
      f .from                        ＝⟨ cat! C ⟩
      f .from ∘ ⌜ id ⌝               ＝˘⟨ ap¡ (g .inv-l) ⟩
      f .from ∘ g .to ∘ g .from      ＝⟨ assoc _ _ _ ⟩
      ⌜ f .from ∘ g .to ⌝ ∘ g .from  ＝⟨ ap! (ap (f .from ∘_) (sym d) ∙ f .inv-r) ⟩
      id ∘ g .from                   ＝⟨ cat! C ⟩
      g .from                        ∎

  inverse-unique
    : {x y : Ob} (p : x ＝ y) {b d : Ob} (q : b ＝ d) {f : x ≅ b} {g : y ≅ d}
    → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
    → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
  inverse-unique p = inverse-unique-internal _ _ p _ _

≅-pathᴾ
  : (p : a ＝ c) (q : b ＝ d) {f : a ≅ b} {g : c ≅ d}
  → ＜ f ._≅_.to ／ (λ i → Hom (p i) (q i)) ＼ g ._≅_.to ＞
  → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
≅-pathᴾ p q {f} {g} r = ≅-pathᴾ-internal p q r (inverse-unique p q {f = f} {g = g} r)

≅-pathᴾ-from
  : (p : a ＝ c) (q : b ＝ d) {f : a ≅ b} {g : c ≅ d}
  → ＜ f ._≅_.from ／ (λ i → Hom (q i) (p i)) ＼ g ._≅_.from ＞
  → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
≅-pathᴾ-from p q {f = f} {g = g} r = ≅-pathᴾ-internal p q (inverse-unique q p {f = f ᵢ⁻¹} {g = g ᵢ⁻¹} r) r

≅-path : {f g : a ≅ b} → f ._≅_.to ＝ g ._≅_.to → f ＝ g
≅-path = ≅-pathᴾ refl refl

≅-path-from : {f g : a ≅ b} → f ._≅_.from ＝ g ._≅_.from → f ＝ g
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
