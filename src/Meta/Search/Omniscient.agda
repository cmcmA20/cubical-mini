{-# OPTIONS --safe #-}
module Meta.Search.Omniscient where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection
open import Meta.Search.Base public
open import Meta.Search.Decidable
open import Meta.Search.Exhaustible
open import Meta.Search.HLevel
open import Meta.Variadic

open import Correspondences.Omniscient
open Correspondences.Omniscient public
  using ( Omniscient₁ ; omniscient₁-β ; omniscient₁-η
        ; omni₁
        ; ∃-decision ; omniscient₁→exhaustible
        ; Omniscient ; omniscient-β ; omniscient-η
        ; omni
        ; Σ-decision ; omniscient→omniscient₁ )

open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Dec.Properties
open import Data.Empty.Base as ⊥
open import Data.Fin.Computational.Instances.FromNat

open import Truncation.Propositional.Base as ∥-∥₁

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  C : (a : A) (b : B a) → Type ℓc
  D : (a : A) (b : B a) (c : C a b) → Type ℓd
  n : HLevel

instance
  Tactic-omni₁ : Tactic-desc (quote Omniscient₁) none
  Tactic-omni₁ .Tactic-desc.args-length = 3
  Tactic-omni₁ .Tactic-desc.goal-selector = 2
  Tactic-omni₁ .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-omni₁ .Tactic-desc.instance-helper = quote omni₁
  Tactic-omni₁ .Tactic-desc.instance-name = quote Omniscient₁

omni₁-tactic-worker = search-tactic-worker Tactic-omni₁
macro omni₁! = omni₁-tactic-worker

instance
  decomp-omn₁-lift : goal-decomposition (quote Omniscient₁) (Lift ℓ′ A)
  decomp-omn₁-lift = decomp (quote lift-omniscient₁) [ `search (quote Omniscient₁) ]

  decomp-omn₁→exh : goal-decomposition (quote Exhaustible) A
  decomp-omn₁→exh = decomp (quote omniscient₁→exhaustible)
    [ `search (quote Omniscient₁) ]

  decomp-dec-∃ : goal-decomposition (quote Dec) ∃[ B ]
  decomp-dec-∃ = decomp (quote ∃-decision) [ `search-under 1 (quote Dec) , `search (quote Omniscient₁) ]


instance
  Tactic-omni : Tactic-desc (quote Omniscient) none
  Tactic-omni .Tactic-desc.args-length = 3
  Tactic-omni .Tactic-desc.goal-selector = 2
  Tactic-omni .Tactic-desc.other-atoms = [ quote _≃_ ]
  Tactic-omni .Tactic-desc.instance-helper = quote omni
  Tactic-omni .Tactic-desc.instance-name = quote Omniscient

omni-tactic-worker = search-tactic-worker Tactic-omni
macro omni! = omni-tactic-worker

omni-prop-helper : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                 → (ΣAB-prop : is-prop Σ[ B ])
                 → Decidable B
                 → Omniscient₁ A
                 → Dec Σ[ B ]
omni-prop-helper ΣAB-prop d omn₁ =
  ∥-∥₁.proj (dec-is-of-hlevel 1 ΣAB-prop) $ (dec-∥-∥₁-equiv ₑ⁻¹) # ∃-decision d omn₁

instance
  decomp-omn-lift : goal-decomposition (quote Omniscient) (Lift ℓ′ A)
  decomp-omn-lift = decomp (quote lift-omniscient) [ `search (quote Omniscient) ]

  decomp-dec-Σ : goal-decomposition (quote Dec) Σ[ B ]
  decomp-dec-Σ = decomp (quote Σ-decision) [ `search-under 1 (quote Dec) , `search (quote Omniscient) ]

  -- TODO: search should try instances before branching into other decomps
  -- decomp-omn→omn₁ : goal-decomposition (quote Omniscient₁) A
  -- decomp-omn→omn₁ = decomp (quote omniscient→omniscient₁)
  --   [ `search (quote Omniscient) ]

  -- same here
  -- decomp-dec-prop-Σ : goal-decomposition (quote Dec) Σ[ B ]
  -- decomp-dec-prop-Σ = decomp (quote omni-prop-helper)
  --   [ `search (quote is-of-hlevel)
  --   , `search-under 1 (quote Dec) , `search (quote Omniscient₁) ]


-- Usage
private
  module _ ⦃ A-omn : Omniscient₁ {ℓ} A ⦄ where
    _ : Omniscient₁ A
    _ = omni₁!

    _ : Exhaustible A
    _ = exhaust!
