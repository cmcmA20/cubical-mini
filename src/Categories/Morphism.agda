{-# OPTIONS --safe --no-exact-split #-}
open import Categories.Base

module Categories.Morphism {o h} (C : Precategory o h) where

open import Meta.Prelude
  hiding (_∘_; id)

open import Meta.Deriving.HLevel
open import Meta.Extensionality
open import Meta.Marker
open import Meta.Record

open import Functions.Embedding
  hiding (_↪_)

open import Categories.Solver

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


-- Epimorphism (epi)

is-epic : a ⇒ b → Type _
is-epic {b} f = {c : Ob} (g h : b ⇒ c) → g ∘ f ＝ h ∘ f → g ＝ h

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
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-monic f
  → is-monic g
  → is-monic (f ∘ g)
monic-∘ fm gm a b α = gm _ _ (fm _ _ (assoc _ _ _ ∙∙ α ∙∙ sym (assoc _ _ _)))

epic-∘
  : {f : b ⇒ c} {g : a ⇒ b}
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

instance
  Refl-mono : Refl _↪_
  Refl-mono .refl .mor = id
  Refl-mono .refl .monic = id-monic

  Refl-epi : Refl _↠_
  Refl-epi .refl .mor = id
  Refl-epi .refl .epic = id-epic

  Trans-mono : Trans _↪_ _↪_ _↪_
  Trans-mono ._∙_ f g = g ∘ₘ f

  Trans-epi : Trans _↠_ _↠_ _↠_
  Trans-epi ._∙_ f g = g ∘ₑ f

-- If `f ∘ g` is monic, then `g` must also be monic.

monic-cancel-l
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-monic (f ∘ g)
  → is-monic g
monic-cancel-l {f} fg-monic h h′ p = fg-monic h h′ $
  sym (assoc _ _ _) ∙∙ ap (f ∘_) p ∙∙ assoc _ _ _

-- Dually, if `f ∘ g` is epic, then `f` must also be epic.

epic-cancel-r
  : {f : b ⇒ c} {g : a ⇒ b}
  → is-epic (f ∘ g)
  → is-epic f
epic-cancel-r {g} fg-epic h h' p = fg-epic h h' $
  assoc _ _ _ ∙∙ ap (_∘ g) p ∙∙ sym (assoc _ _ _)


-- Postcomposition with a mono is an embedding.

monic-postcomp-is-embedding
  : {f : b ⇒ c}
  → is-monic f
  → is-embedding {A = a ⇒ b} (f ∘_)
monic-postcomp-is-embedding monic =
  set-injective→is-embedding (Hom-set _ _) (monic _ _)

-- Likewise, precomposition with an epi is an embedding.

epic-precomp-embedding
  : {f : a ⇒ b}
  → is-epic f
  → is-embedding {A = b ⇒ c} (_∘ f)
epic-precomp-embedding epic =
  set-injective→is-embedding (Hom-set _ _) (epic _ _)


-- Sections

id-has-section : has-section (id {a})
id-has-section .section = id
id-has-section .is-section = id-l _

section-of-∘
  : {f : c ⇒ b} {g : b ⇒ c} {h : b ⇒ a} {i : a ⇒ b}
  → f section-of g → h section-of i
  → (h ∘ f) section-of (g ∘ i)
section-of-∘ {f} {g} {h} {i} fg-sect hi-sect =
  (g ∘ i) ∘ h ∘ f    ~⟨ cat! C ⟩
  g ∘ ⌜ i ∘ h ⌝ ∘ f  ~⟨ ap! (hi-sect) ⟩
  g ∘ ⌜ id ∘ f ⌝     ~⟨ ap! (id-l _) ⟩
  g ∘ f              ~⟨ fg-sect ⟩
  id                 ∎

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
has-section→epic {f = f} f-sect g h p =
  g                            ~⟨ id-r _ ⟨
  g ∘ ⌜ id ⌝                   ~⟨ ap¡ (f-sect .is-section) ⟨
  g ∘ f ∘ f-sect .section      ~⟨ assoc _ _ _ ⟩
  ⌜ g ∘ f ⌝ ∘ f-sect .section  ~⟨ ap! p ⟩
  (h ∘ f) ∘ f-sect .section    ~⟨ assoc _ _ _ ⟨
  h ∘ ⌜ f ∘ f-sect .section ⌝  ~⟨ ap! (f-sect .is-section) ⟩
  h ∘ id                       ~⟨ id-r _ ⟩
  h                            ∎


-- Retracts

id-has-retract : has-retract (id {a})
id-has-retract .retract = id
id-has-retract .is-retract = id-l _

retract-of-∘
  : {f : c ⇒ b} {g : b ⇒ c} {h : b ⇒ a} {i : a ⇒ b}
  → f retract-of g → h retract-of i
  → (h ∘ f) retract-of (g ∘ i)
retract-of-∘ = flip section-of-∘

retract-∘
  : {f : b ⇒ c} {g : a ⇒ b}
  → has-retract f → has-retract g
  → has-retract (f ∘ g)
retract-∘ f-ret g-ret .retract = g-ret .retract ∘ f-ret .retract
retract-∘ f-ret g-ret .is-retract =
  retract-of-∘ (f-ret .is-retract) (g-ret .is-retract)


-- If `f` has a retract, then `f` is monic.

has-retract→monic
  : {f : Hom a b}
  → has-retract f
  → is-monic f
has-retract→monic {f} f-ret g h p =
  g                           ~⟨ id-l _ ⟨
  ⌜ id ⌝ ∘ g                  ~⟨ ap¡ (f-ret .is-retract) ⟨
  (f-ret .retract ∘ f) ∘ g    ~⟨ assoc _ _ _ ⟨
  f-ret .retract ∘ ⌜ f ∘ g ⌝  ~⟨ ap! p ⟩
  f-ret .retract ∘ f ∘ h      ~⟨ assoc _ _ _ ⟩
  ⌜ f-ret .retract ∘ f ⌝ ∘ h  ~⟨ ap! (f-ret .is-retract) ⟩
  id ∘ h                      ~⟨ id-l _ ⟩
  h                           ∎


-- A section that is also epic is a retract.

section-of+epic→retract-of
  : {s : b ⇒ a} {r : a ⇒ b}
  → s section-of r
  → is-epic s
  → s retract-of r
section-of+epic→retract-of {s} {r} sect epic =
  epic (s ∘ r) id $
    (s ∘ r) ∘ s    ~⟨ assoc s r s ⟨
    s ∘ ⌜ r ∘ s ⌝  ~⟨ ap! sect ⟩
    s ∘ id         ~⟨ cat! C ⟩
    id ∘ s         ∎


-- Dually, a retract that is also monic is a section.

retract-of+monic→section-of
  : {s : b ⇒ a} {r : a ⇒ b}
  → r retract-of s
  → is-monic r
  → r section-of s
retract-of+monic→section-of {s = s} {r = r} ret monic =
  monic (s ∘ r) id $
    r ∘ s ∘ r      ~⟨ assoc r s r ⟩
    ⌜ r ∘ s ⌝ ∘ r  ~⟨ ap! ret ⟩
    id ∘ r         ~⟨ cat! C ⟩
    r ∘ id         ∎


has-retract+epic→has-section
  : {f : Hom a b}
  → has-retract f
  → is-epic f
  → has-section f
has-retract+epic→has-section ret epic .section = ret .retract
has-retract+epic→has-section ret epic .is-section =
  section-of+epic→retract-of (ret .is-retract) epic

has-section+monic→has-retract
  : {f : Hom a b}
  → has-section f
  → is-monic f
  → has-retract f
has-section+monic→has-retract sect monic .retract = sect .section
has-section+monic→has-retract sect monic .is-retract =
  retract-of+monic→section-of (sect .is-section) monic


-- Isomorphism (iso)

open Inverses

instance
  H-Level-inverses
    : {f : a ⇒ b} {g : b ⇒ a} {n : HLevel} ⦃ _ : n ≥ʰ 1 ⦄
    → H-Level n (Inverses f g)
  H-Level-inverses ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (≅→is-of-hlevel! 1 Inverses-Iso)

inverses-are-prop : {f : a ⇒ b} {g : b ⇒ a} → is-prop (Inverses f g)
inverses-are-prop = hlevel 1

opaque
  is-invertible-is-prop : {f : a ⇒ b} → is-prop (is-invertible f)
  is-invertible-is-prop {a} {b} {f} g h = p where
    module g = is-invertible g
    module h = is-invertible h

    g~h : g.inv ＝ h.inv
    g~h =
      g.inv              ~⟨ sym (id-r _) ∙ ap² _∘_ refl (sym h.inv-o) ⟩
      g.inv ∘ f ∘ h.inv  ~⟨ assoc _ _ _ ∙∙ ap² _∘_ g.inv-i refl ∙∙ id-l _ ⟩
      h.inv              ∎

    p : g ＝ h
    p i .is-invertible.inv = g~h i
    p i .is-invertible.inverses =
     is-prop→pathᴾ (λ i → inverses-are-prop {g = g~h i}) g.inverses h.inverses i

id-invertible : is-invertible (id {a})
id-invertible .is-invertible.inv = id
id-invertible .is-invertible.inverses .inv-o = id-l id
id-invertible .is-invertible.inverses .inv-i = id-l id


open Iso

Isoᶜ : Ob → Ob → Type h
Isoᶜ = Iso Hom Hom

instance
  ≅-Cat-Ob : ≅-notation Ob Ob (𝒰 h)
  ≅-Cat-Ob ._≅_ = Isoᶜ
  {-# INCOHERENT ≅-Cat-Ob #-}

Inverses-∘ : {f : a ⇒ b} {f⁻¹ : b ⇒ a} {g : b ⇒ c} {g⁻¹ : c ⇒ b}
           → Inverses f f⁻¹ → Inverses g g⁻¹ → Inverses (g ∘ f) (f⁻¹ ∘ g⁻¹)
Inverses-∘ {f} {f⁻¹} {g} {g⁻¹} finv ginv = record { inv-o = l ; inv-i = r } where
  module finv = Inverses finv
  module ginv = Inverses ginv

  opaque
    l : (g ∘ f) ∘ f⁻¹ ∘ g⁻¹ ＝ id
    l = (g ∘ f) ∘ f⁻¹ ∘ g⁻¹    ~⟨ cat! C ⟩
        g ∘ ⌜ f ∘ f⁻¹ ⌝ ∘ g⁻¹  ~⟨ ap! finv.inv-o ⟩
        g ∘ id ∘ g⁻¹           ~⟨ cat! C ⟩
        g ∘ g⁻¹                ~⟨ ginv.inv-o ⟩
        id                     ∎

    r : (f⁻¹ ∘ g⁻¹) ∘ g ∘ f ＝ id
    r = (f⁻¹ ∘ g⁻¹) ∘ g ∘ f    ~⟨ cat! C ⟩
        f⁻¹ ∘ ⌜ g⁻¹ ∘ g ⌝ ∘ f  ~⟨ ap! ginv.inv-i ⟩
        f⁻¹ ∘ id ∘ f           ~⟨ cat! C ⟩
        f⁻¹ ∘ f                ~⟨ finv.inv-i ⟩
        id                     ∎


invertible-∘
  : {f : b ⇒ c} {g : a ⇒ b}
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
  : {f : Hom a b}
  → (f-inv : is-invertible f)
  → is-invertible (is-invertible.inv f-inv)
_invertible⁻¹ {f = f} f-inv .is-invertible.inv = f
_invertible⁻¹ f-inv .is-invertible.inverses .inv-o =
  is-invertible.inv-i f-inv
_invertible⁻¹ f-inv .is-invertible.inverses .inv-i =
  is-invertible.inv-o f-inv


private
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

opaque
  private
    inverse-unique-internal
      : (x y : Ob) (p : x ＝ y) (b d : Ob) (q : b ＝ d) {f : x ≅ b} {g : y ≅ d}
      → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
      → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
    inverse-unique-internal x = J>! λ y → J>! λ {f} {g} d →
      f .from                        ~⟨ cat! C ⟩
      f .from ∘ ⌜ id ⌝               ~⟨ ap¡ (g .inv-o) ⟨
      f .from ∘ g .to ∘ g .from      ~⟨ assoc _ _ _ ⟩
      ⌜ f .from ∘ g .to ⌝ ∘ g .from  ~⟨ ap! (ap (f .from ∘_) (sym d) ∙ f .inv-i) ⟩
      id ∘ g .from                   ~⟨ cat! C ⟩
      g .from                        ∎

  inverse-unique
    : {x y : Ob} (p : x ＝ y) {b d : Ob} (q : b ＝ d) {f : x ≅ b} {g : y ≅ d}
    → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
    → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
  inverse-unique p = inverse-unique-internal _ _ p _ _

≅-pathᴾ
  : (p : a ＝ c) (q : b ＝ d) {f : a ≅ b} {g : c ≅ d}
  → ＜ f .to ／ (λ i → Hom (p i) (q i)) ＼ g .to ＞
  → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
≅-pathᴾ p q {f} {g} r = ≅-pathᴾ-internal p q r (inverse-unique p q {f = f} {g = g} r)

≅-pathᴾ-from
  : (p : a ＝ c) (q : b ＝ d) {f : a ≅ b} {g : c ≅ d}
  → ＜ f .from ／ (λ i → Hom (q i) (p i)) ＼ g .from ＞
  → ＜ f ／ (λ i → p i ≅ q i) ＼ g ＞
≅-pathᴾ-from p q {f = f} {g = g} r = ≅-pathᴾ-internal p q (inverse-unique q p {f = f ⁻¹} {g = g ⁻¹} r) r

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
