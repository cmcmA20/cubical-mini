{-# OPTIONS --safe #-}
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.Morphism {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) where

import Cat.Morphism

open Displayed ℰ
open Cat.Morphism ℬ

private variable
  a b c d : Ob
  f g : Hom a b
  a′ b′ c′ : Ob[ a ]

-- TODO mono, epi

-- iso

record Inverses[_]
  {a b : Ob} {a′ : Ob[ a ]} {b′ : Ob[ b ]}
  {f : Hom a b} {g : Hom b a}
  (inv : Inverses f g)
  (f′ : Hom[ f ] a′ b′) (g′ : Hom[ g ] b′ a′)
  : Type ℓ′
  where
  no-eta-equality
  field
    inv-lᵈ : f′ ∘ᵈ g′ ＝[ Inverses.inv-o inv ] idᵈ
    inv-rᵈ : g′ ∘ᵈ f′ ＝[ Inverses.inv-i inv ] idᵈ

record quasi-inverse[_]
  {a b a′ b′} {f : Hom a b}
  (f-inv : quasi-inverse f)
  (f′ : Hom[ f ] a′ b′)
  : Type ℓ′
  where
  no-eta-equality
  field
    invᵈ      : Hom[ quasi-inverse.inv f-inv ] b′ a′
    inversesᵈ : Inverses[ quasi-inverse.inverses f-inv ] f′ invᵈ

  open Inverses[_] inversesᵈ public

record _≅[_]_
  {a b} (a′ : Ob[ a ]) (i : a ≅ b) (b′ : Ob[ b ])
  : Type ℓ′
  where
  no-eta-equality
  open Iso
  field
    toᵈ       : Hom[ i .to ] a′ b′
    fromᵈ     : Hom[ i .from ] b′ a′
    inversesᵈ : Inverses[ i .inverses ] toᵈ fromᵈ

  open Inverses[_] inversesᵈ public

-- open _≅[_]_ public

_≅↓_ : {x : Ob} (A B : Ob[ x ]) → Type ℓ′
_≅↓_ = _≅[ refl ]_

quasi-inverse↓ : {x : Ob} {x′ x″ : Ob[ x ]} → Hom[ id ] x′ x″ → Type _
quasi-inverse↓ = quasi-inverse[ id-qinv ]

make-invertible↓
  : ∀ {x} {x′ x″ : Ob[ x ]} {f′ : Hom[ id ] x′ x″}
  → (g′ : Hom[ id ] x″ x′)
  → f′ ∘ᵈ g′ ＝[ id-r _ ] idᵈ
  → g′ ∘ᵈ f′ ＝[ id-r _ ] idᵈ
  → quasi-inverse↓ f′
make-invertible↓ g′ p q .quasi-inverse[_].invᵈ = g′
make-invertible↓ g′ p q .quasi-inverse[_].inversesᵈ .Inverses[_].inv-lᵈ = p
make-invertible↓ g′ p q .quasi-inverse[_].inversesᵈ .Inverses[_].inv-rᵈ = q

opaque
  Inverses[]-are-prop
    : ⦃ _ : ∀ {h} → H-Level 2 (Hom[ h ] a′ a′) ⦄
      ⦃ _ : ∀ {h} → H-Level 2 (Hom[ h ] b′ b′) ⦄
    → (inv : Inverses f g)
    → (f′ : Hom[ f ] a′ b′) (g′ : Hom[ g ] b′ a′)
    → is-prop (Inverses[ inv ] f′ g′)
  Inverses[]-are-prop inv f′ g′ inv[] inv[]′ i .Inverses[_].inv-lᵈ =
    is-set→squareᴾ (λ i j → hlevel 2)
      refl (Inverses[_].inv-lᵈ inv[]) (Inverses[_].inv-lᵈ inv[]′) refl i
  Inverses[]-are-prop inv f′ g′ inv[] inv[]′ i .Inverses[_].inv-rᵈ =
    is-set→squareᴾ (λ i j → hlevel 2)
      refl (Inverses[_].inv-rᵈ inv[]) (Inverses[_].inv-rᵈ inv[]′) refl i

  -- TODO
  -- quasi-inverse[]-is-prop
  --   : ∀ {a b a′ b′} {f : Hom a b}
  --   → (f-inv : quasi-inverse f)
  --   → (f′ : Hom[ f ] a′ b′)
  --   → is-prop (quasi-inverse[ f-inv ] f′)

open Iso
open _≅[_]_

make-iso[_]
  : ∀ {a b : Ob} {a′ b′}
  → (iso : a ≅ b)
  → (f′ : Hom[ iso .to ] a′ b′) (g′ : Hom[ iso .from ] b′ a′)
  → f′ ∘ᵈ g′ ＝[ iso .inv-o ] idᵈ
  → g′ ∘ᵈ f′ ＝[ iso .inv-i ] idᵈ
  → a′ ≅[ iso ] b′
make-iso[ inv ] f′ g′ p q .toᵈ = f′
make-iso[ inv ] f′ g′ p q .fromᵈ = g′
make-iso[ inv ] f′ g′ p q .inversesᵈ .Inverses[_].inv-lᵈ = p
make-iso[ inv ] f′ g′ p q .inversesᵈ .Inverses[_].inv-rᵈ = q

make-vertical-iso
  : ∀ {x} {x′ x″ : Ob[ x ]}
  → (f′ : Hom[ id ] x′ x″) (g′ : Hom[ id ] x″ x′)
  → f′ ∘ᵈ g′ ＝[ id-r _ ] idᵈ
  → g′ ∘ᵈ f′ ＝[ id-r _ ] idᵈ
  → x′ ≅↓ x″
make-vertical-iso = make-iso[ refl ]

invertible[]→iso[]
  : ∀ {a b a′ b′} {f : Hom a b} {f′ : Hom[ f ] a′ b′}
  → {i : quasi-inverse f}
  → quasi-inverse[ i ] f′
  → a′ ≅[ qinv→≅ f i ] b′
invertible[]→iso[] {f′ = f′} i =
  make-iso[ _ ]
    f′
    (quasi-inverse[_].invᵈ i)
    (quasi-inverse[_].inv-lᵈ i)
    (quasi-inverse[_].inv-rᵈ i)

id-iso↓ : ∀ {x} {x′ : Ob[ x ]} → x′ ≅↓ x′
id-iso↓ = make-iso[ refl ] idᵈ idᵈ (id-rᵈ idᵈ) (id-rᵈ idᵈ)


-- equiv

record has-retraction[_]
  {a b : Ob} {a′ : Ob[ a ]} {b′ : Ob[ b ]}
  {f : Hom a b} (hr : has-retraction f)
  (f′ : Hom[ f ] a′ b′) : Type ℓ′
  where
  no-eta-equality
  field
    retractionᵈ    : Hom[ hr .retraction ] b′ a′
    is-retractionᵈ : retractionᵈ ∘ᵈ f′ ＝[ hr .is-retraction ] idᵈ

record has-section[_]
  {a b : Ob} {a′ : Ob[ a ]} {b′ : Ob[ b ]}
  {f : Hom a b} (hs : has-section f)
  (f′ : Hom[ f ] a′ b′) : Type ℓ′
  where
  no-eta-equality
  field
    sectionᵈ    : Hom[ hs .section ] b′ a′
    is-sectionᵈ : f′ ∘ᵈ sectionᵈ ＝[ hs .is-section ] idᵈ

is-biinv[_] : ∀ {a b a′ b′} {f : Hom a b} (f-bi : is-biinv f) (f′ : Hom[ f ] a′ b′) → Type ℓ′
is-biinv[_] (hr , hs) f′ = has-retraction[ hr ] f′ × has-section[ hs ] f′

record _≊[_]_
  {a b} (a′ : Ob[ a ]) (e : a ≊ b) (b′ : Ob[ b ]) : Type ℓ′
  where
  no-eta-equality
  open Biinv
  field
    toᵈ        : Hom[ e .to ] a′ b′
    has-biinvᵈ : is-biinv[ e .has-biinv ] toᵈ

  open has-retraction[_] (has-biinvᵈ .fst)
    renaming (retractionᵈ to fromᵈ ; is-retractionᵈ to from-is-retractionᵈ)
    public
  open has-section[_] (has-biinvᵈ .snd) public

open _≊[_]_

_≊↓_ : {x : Ob} (A B : Ob[ x ]) → Type ℓ′
_≊↓_ = _≊[ refl ]_

is-biinv↓ : {x : Ob} {x′ x″ : Ob[ x ]} → Hom[ id ] x′ x″ → Type _
is-biinv↓ = is-biinv[ (make-retract id (id-l id)) , make-section id (id-l id) ]

open Biinv
open _≊[_]_

make-equiv[_]
  : ∀ {a b : Ob} {a′ b′}
  → (e : a ≊ b)
  → (f′ : Hom[ e .to ] a′ b′)
    (r′ : Hom[ e .from ] b′ a′) (rr′ : r′ ∘ᵈ f′ ＝[ e .from-is-retraction ] idᵈ)
    (s′ : Hom[ e .section ] b′ a′) (ss′ : f′ ∘ᵈ s′ ＝[ e .is-section ] idᵈ)
  → a′ ≊[ e ] b′
make-equiv[ _ ] f′ _  _   _  _   .toᵈ = f′
make-equiv[ _ ] _  r′ _   _  _   .has-biinvᵈ .fst .has-retraction[_].retractionᵈ = r′
make-equiv[ _ ] _  _  rr′ _  _   .has-biinvᵈ .fst .has-retraction[_].is-retractionᵈ = rr′
make-equiv[ _ ] _  _  _   s′ _   .has-biinvᵈ .snd .has-section[_].sectionᵈ = s′
make-equiv[ _ ] _  _  _   _  ss′ .has-biinvᵈ .snd .has-section[_].is-sectionᵈ = ss′

make-vertical-equiv
  : ∀ {x} {x′ x″ : Ob[ x ]}
  → (f′ : Hom[ id ] x′ x″)
    (r′ : Hom[ id ] x″ x′) (rr′ : r′ ∘ᵈ f′ ＝[ id-r id ] idᵈ)
    (s′ : Hom[ id ] x″ x′) (ss′ : f′ ∘ᵈ s′ ＝[ id-r id ] idᵈ)
  → x′ ≊↓ x″
make-vertical-equiv = make-equiv[ refl ]

-- TODO
-- ≊[]-path
--   : {x y : Ob} {A : Ob[ x ]} {B : Ob[ y ]} {e : x ≊ y}
--     {p q : A ≊[ e ] B}
--   → p .toᵈ ＝ q .toᵈ
--   → p ＝ q
-- ≊[]-path r = {!!}

id-equiv↓ : ∀ {x} {x′ : Ob[ x ]} → x′ ≊↓ x′
id-equiv↓ = make-equiv[ refl ] idᵈ idᵈ (id-rᵈ idᵈ) idᵈ (id-rᵈ idᵈ)
