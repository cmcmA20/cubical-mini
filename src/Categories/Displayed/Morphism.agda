{-# OPTIONS --safe #-}
open import Categories.Displayed.Base
open import Categories.Prelude

module Categories.Displayed.Morphism {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) where

import Categories.Morphism
import Categories.Displayed.Reasoning

open Displayed ℰ
open Categories.Morphism ℬ
open Categories.Displayed.Reasoning ℰ

private variable
  a b c d : Ob
  f : Hom a b
  a′ b′ c′ : Ob[ a ]

-- TODO mono, epi

record Inverses[_]
  {a b a′ b′} {f : Hom a b} {g : Hom b a}
  (inv : Inverses f g)
  (f′ : Hom[ f ] a′ b′) (g′ : Hom[ g ] b′ a′)
  : Type ℓ′
  where
  no-eta-equality
  field
    inv-lᵈ : f′ ∘ᵈ g′ ＝[ Inverses.inv-l inv ] idᵈ
    inv-rᵈ : g′ ∘ᵈ f′ ＝[ Inverses.inv-r inv ] idᵈ

record is-invertible[_]
  {a b a′ b′} {f : Hom a b}
  (f-inv : is-invertible f)
  (f′ : Hom[ f ] a′ b′)
  : Type ℓ′
  where
  no-eta-equality
  field
    invᵈ      : Hom[ is-invertible.inv f-inv ] b′ a′
    inversesᵈ : Inverses[ is-invertible.inverses f-inv ] f′ invᵈ

  open Inverses[_] inversesᵈ public

record _≅[_]_
  {a b} (a′ : Ob[ a ]) (i : a ≅ b) (b′ : Ob[ b ])
  : Type ℓ′
  where
  no-eta-equality
  field
    toᵈ       : Hom[ i .to ] a′ b′
    fromᵈ     : Hom[ i .from ] b′ a′
    inversesᵈ : Inverses[ i .inverses ] toᵈ fromᵈ

  open Inverses[_] inversesᵈ public

open _≅[_]_ public

_≅↓_ : {x : Ob} (A B : Ob[ x ]) → Type ℓ′
_≅↓_ = _≅[ id-iso ]_

is-invertible↓ : {x : Ob} {x′ x″ : Ob[ x ]} → Hom[ id ] x′ x″ → Type _
is-invertible↓ = is-invertible[ id-invertible ]

make-invertible↓
  : ∀ {x} {x′ x″ : Ob[ x ]} {f′ : Hom[ id ] x′ x″}
  → (g′ : Hom[ id ] x″ x′)
  → f′ ∘ᵈ g′ ＝[ id-l _ ] idᵈ
  → g′ ∘ᵈ f′ ＝[ id-l _ ] idᵈ
  → is-invertible↓ f′
make-invertible↓ g′ p q .is-invertible[_].invᵈ = g′
make-invertible↓ g′ p q .is-invertible[_].inversesᵈ .Inverses[_].inv-lᵈ = p
make-invertible↓ g′ p q .is-invertible[_].inversesᵈ .Inverses[_].inv-rᵈ = q

opaque
  unfolding is-of-hlevel
  Inverses[]-are-prop
    : ∀ {a b a′ b′} {f : Hom a b} {g : Hom b a}
    → (inv : Inverses f g)
    → (f′ : Hom[ f ] a′ b′) (g′ : Hom[ g ] b′ a′)
    → is-prop (Inverses[ inv ] f′ g′)
  Inverses[]-are-prop inv f′ g′ inv[] inv[]′ i .Inverses[_].inv-lᵈ =
    is-set→squareᴾ (λ i j → Hom[ Inverses.inv-l inv j ]-set _ _)
      refl (Inverses[_].inv-lᵈ inv[]) (Inverses[_].inv-lᵈ inv[]′) refl i
  Inverses[]-are-prop inv f′ g′ inv[] inv[]′ i .Inverses[_].inv-rᵈ =
    is-set→squareᴾ (λ i j → Hom[ Inverses.inv-r inv j ]-set _ _)
      refl (Inverses[_].inv-rᵈ inv[]) (Inverses[_].inv-rᵈ inv[]′) refl i

  -- TODO
  -- is-invertible[]-is-prop
  --   : ∀ {a b a′ b′} {f : Hom a b}
  --   → (f-inv : is-invertible f)
  --   → (f′ : Hom[ f ] a′ b′)
  --   → is-prop (is-invertible[ f-inv ] f′)

make-iso[_]
  : ∀ {a b a′ b′}
  → (iso : a ≅ b)
  → (f′ : Hom[ iso .to ] a′ b′) (g′ : Hom[ iso .from ] b′ a′)
  → f′ ∘ᵈ g′ ＝[ iso .inv-l ] idᵈ
  → g′ ∘ᵈ f′ ＝[ iso .inv-r ] idᵈ
  → a′ ≅[ iso ] b′
make-iso[ inv ] f′ g′ p q .toᵈ = f′
make-iso[ inv ] f′ g′ p q .fromᵈ = g′
make-iso[ inv ] f′ g′ p q .inversesᵈ .Inverses[_].inv-lᵈ = p
make-iso[ inv ] f′ g′ p q .inversesᵈ .Inverses[_].inv-rᵈ = q

make-vertical-iso
  : ∀ {x} {x′ x″ : Ob[ x ]}
  → (f′ : Hom[ id ] x′ x″) (g′ : Hom[ id ] x″ x′)
  → f′ ∘ᵈ g′ ＝[ id-l _ ] idᵈ
  → g′ ∘ᵈ f′ ＝[ id-l _ ] idᵈ
  → x′ ≅↓ x″
make-vertical-iso = make-iso[ id-iso ]

invertible[]→iso[]
  : ∀ {a b a′ b′} {f : Hom a b} {f′ : Hom[ f ] a′ b′}
  → {i : is-invertible f}
  → is-invertible[ i ] f′
  → a′ ≅[ invertible→iso f i ] b′
invertible[]→iso[] {f′ = f′} i =
  make-iso[ _ ]
    f′
    (is-invertible[_].invᵈ i)
    (is-invertible[_].inv-lᵈ i)
    (is-invertible[_].inv-rᵈ i)

-- TODO
-- ≅[]-path
--   : {x y : Ob} {A : Ob[ x ]} {B : Ob[ y ]} {f : x ≅ y}
--     {p q : A ≅[ f ] B}
--   → p .to′ ＝ q .to′
--   → p ＝ q

id-iso↓ : ∀ {x} {x′ : Ob[ x ]} → x′ ≅↓ x′
id-iso↓ = make-iso[ id-iso ] idᵈ idᵈ (id-lᵈ idᵈ) (id-lᵈ idᵈ)
