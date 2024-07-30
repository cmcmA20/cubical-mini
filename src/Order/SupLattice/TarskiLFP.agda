{-# OPTIONS --safe #-}
module Order.SupLattice.TarskiLFP where

open import Categories.Prelude
open import Meta.Prelude
open import Foundations.Equiv.Size

open import Data.Empty
open import Data.Unit
--open import Data.Sum
--open import Data.List

open import Combinatorics.Power

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice
open import Order.SupLattice.SmallBasis
import Order.Reasoning

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
        where

  open Poset P

  has-lfp : (Ob → Ob) → 𝒰 (o ⊔ ℓ)
  has-lfp f = Σ[ p ꞉ Ob ] (f p ＝ p) × ((a : Ob) → f a ＝ a → p ≤ a)

  has-lfp-is-prop : (f : Ob → Ob) → is-prop (has-lfp f)
  has-lfp-is-prop f (p₁ , fp₁ , l₁) (p₂ , fp₂ , l₂) =
    Σ-prop-path (λ x → hlevel 1)
                (≤-antisym (l₁ p₂ fp₂) (l₂ p₁ fp₁))

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
        where

  open Poset P
  open is-sup-lattice L
  open is-basis h

  c-closure : {ℓ″ : Level} (S : ℙ B ℓ″) → 𝒰 (ℓsuc ℓ′ ⊔ ℓ″)
  c-closure S = (U : ℙ B ℓ′) → U ⊆ S → (b : B) → b ≤ᴮ (sup (ℙ→fam β U .snd)) → b ∈ S

  _closure : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
           → {ℓ″ : Level} (S : ℙ B ℓ″)
           → 𝒰 (o ⊔ ℓ′ ⊔ ℓ″)
  (ϕ closure) S = (a : Ob)
                → (b : B)
                → (b , a) ∈ ϕ
                → ((b' : B) → b' ≤ᴮ a → b' ∈ S)
                → b ∈ S

  data 𝓘 (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) : B → 𝒰 (o ⊔ ℓsuc ℓ′) where
    c-closed : (U : ℙ B ℓ′) → ({b : B} → b ∈ U → 𝓘 ϕ b)
             → (b : B) → b ≤ᴮ (sup (ℙ→fam β U .snd)) → 𝓘 ϕ b
    ϕ-closed : (a : Ob) → (b : B) → (b , a) ∈ ϕ
              → ((b' : B) → b' ≤ᴮ a → 𝓘 ϕ b')
              → 𝓘 ϕ b
    𝓘-trunc : (b : B) → is-prop (𝓘 ϕ b)

  𝓘nd : ℙ (B × Ob) (o ⊔ ℓ′) → ℙ B (o ⊔ ℓsuc ℓ′)
  𝓘nd ϕ b = el (𝓘 ϕ b) (𝓘-trunc b)

  𝓘nd-is-c-closed : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) → c-closure (𝓘nd ϕ)
  𝓘nd-is-c-closed ϕ = c-closed

  𝓘nd-is-ϕ-closed : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) → (ϕ closure) (𝓘nd ϕ)
  𝓘nd-is-ϕ-closed ϕ = ϕ-closed

  𝓘nd-is-initial : {ℓ″ : Level} (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) (P : ℙ B ℓ″)
                 → c-closure P
                 → (ϕ closure) P
                 → 𝓘nd ϕ ⊆ P
  𝓘nd-is-initial ϕ P cc ϕc (c-closed U sub b le) = cc U (λ ua → 𝓘nd-is-initial ϕ P cc ϕc (sub ua)) b le
  𝓘nd-is-initial ϕ P cc ϕc (ϕ-closed a b m f)    = ϕc a b m (λ b' le → 𝓘nd-is-initial ϕ P cc ϕc (f b' le))
  𝓘nd-is-initial ϕ P cc ϕc (𝓘-trunc b x y i)     = hlevel 1 (𝓘nd-is-initial ϕ P cc ϕc x) (𝓘nd-is-initial ϕ P cc ϕc y) i

