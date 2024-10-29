{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Unique where

open import Prelude
open import Data.Empty
open import Data.Reflects
open import Data.List
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Related
open import Data.List.Membership

private variable
  ℓ : Level
  A : 𝒰 ℓ
  x y : A
  xs : List A

data Uniq {ℓ} {A : 𝒰 ℓ} : List A → 𝒰 ℓ where
  []ᵘ : Uniq []
  _∷ᵘ_ : x ∉ xs → Uniq xs → Uniq (x ∷ xs)

Uniq-is-prop : is-prop (Uniq xs)
Uniq-is-prop  []ᵘ         []ᵘ        = refl
Uniq-is-prop (nx1 ∷ᵘ u1) (nx2 ∷ᵘ u2) = ap² _∷ᵘ_ prop! (Uniq-is-prop u1 u2)

-- homotopy uniqueness

Uniq-set→is-unique : {xs : List A}
                   → is-set A → Uniq xs → is-unique xs
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (here e1)   (here e2)   = ap here (sa z x e1 e2)
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (here e1)   (there hz2) = absurd (nx (subst (_∈ₗ xs) e1 hz2))
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (there hz1) (here e2)   = absurd (nx (subst (_∈ₗ xs) e2 hz1))
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (there hz1) (there hz2) = ap there (Uniq-set→is-unique sa u z hz1 hz2)

is-unique→Uniq : is-unique xs → Uniq xs
is-unique→Uniq {xs = []}     _ = []ᵘ
is-unique→Uniq {xs = x ∷ xs} u =
  (λ hx → false! (u x (here refl) (there hx)))
  ∷ᵘ is-unique→Uniq λ y h1 h2 → there-inj (u y (there h1) (there h2))

-- relatedness/sortedness with irreflexive relation implies uniqueness

related→uniq : {ℓ′ : Level} {x : A} {xs : List A} {R : A → A → 𝒰 ℓ′} → ⦃ Trans R ⦄
             → (∀ {x} → ¬ R x x)
             → Related R x xs → Uniq (x ∷ xs)
related→uniq     {xs = []}         _    _           = false! ∷ᵘ []ᵘ
related→uniq {x} {xs = y ∷ xs} {R} irr (rxy ∷ʳ rel) =
  ¬Any-∷ (contra (λ e → subst (R x) (e ⁻¹) rxy) irr)
         (λ hx → irr (rxy ∙ All→∀∈ (related→all rel) x hx))
  ∷ᵘ related→uniq irr rel

sorted→uniq : {ℓ′ : Level} {xs : List A} {R : A → A → 𝒰 ℓ′} → ⦃ Trans R ⦄
            → (∀ {x} → ¬ R x x)
            → Sorted R xs → Uniq xs
sorted→uniq {xs = []}     irr []ˢ      = []ᵘ
sorted→uniq {xs = x ∷ xs} irr (∷ˢ rel) = related→uniq irr rel

