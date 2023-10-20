{-# OPTIONS --safe #-}
module Structures.Subtype where

open import Foundations.Base
open import Foundations.Pi
open import Foundations.Sigma

open import Meta.Search.HLevel
open import Meta.SIP

open import Structures.Fibration
open import Structures.IdentitySystem
open import Structures.n-Type

open import Correspondences.Powerset.Base

open import Functions.Embedding

private variable
  ℓ ℓᵗ : Level
  T : Type ℓᵗ

Subtype : (ℓ : Level) → Type ℓ → Type _
Subtype ℓ T = Σ[ X ꞉ Type ℓ ] X ↪ T

@0 subtype≃ℙ : Subtype ℓ T ≃ ℙ T
subtype≃ℙ = subtype-classifier ∙ₑ Π-cod-≃ λ _ → iso→equiv n-Type-iso ₑ⁻¹

@0 subtype-is-set : is-set (Subtype ℓ T)
subtype-is-set = is-of-hlevel-≃ 2 subtype≃ℙ hlevel!

@0 subtype-is-of-hlevel : ∀ n → is-of-hlevel (2 + n) (Subtype ℓ T)
subtype-is-of-hlevel n = is-of-hlevel-+-left 2 n subtype-is-set

instance
  decomp-hlevel-subtype : goal-decomposition (quote is-of-hlevel) (Subtype ℓ T)
  decomp-hlevel-subtype = decomp (quote subtype-is-of-hlevel) (`level-minus 2 ∷ [])

module Path where

  Code : Subtype ℓ T → Subtype ℓ T → Type _
  Code (X , f , _) (Y , g , _) = Σ[ e ꞉ X ≃ Y ] (f ＝ g ∘ e .fst)

  @0 code≃path : (U V : Subtype ℓ T) → Code U V ≃ (U ＝ V)
  code≃path U@(X , f , f-emb) V@(Y , g , g-emb) =
    Code U V                                         ≃⟨⟩
    Σ[ e ꞉ X ≃ Y ] (f ＝ g ∘ e .fst)                 ≃⟨ Σ-ap-snd (λ _ → fun-ext-≃) ⟩
    Σ[ e ꞉ X ≃ Y ] Π[ x ꞉ X ] (f x ＝ g (e .fst x))  ≃⟨ SIP (fibration-str-is-univalent _ _) ⟩
    (X , f) ＝ (Y , g)                               ≃⟨ Σ-prop-path-≃ hlevel! ⟩
    ((X , f) , f-emb) ＝ ((Y , g) , g-emb)           ≃˘⟨ ap-≃ Σ-assoc ⟩
    U ＝ V                                           ≃∎

  @0 code-is-prop : (U V : Subtype ℓ T) → is-prop (Code U V)
  code-is-prop U V = is-of-hlevel-≃ 1 (code≃path U V) (path-is-of-hlevel′ 1 subtype-is-set U V)

  @0 code-is-of-hlevel : {U V : Subtype ℓ T} → ∀ n → is-of-hlevel (suc n) (Code U V)
  code-is-of-hlevel {U} {V} n = is-of-hlevel-+-left 1 n (code-is-prop U V)

  instance
    decomp-hlevel-code : {U V : Subtype ℓ T} → goal-decomposition (quote is-of-hlevel) (Code U V)
    decomp-hlevel-code = decomp (quote code-is-of-hlevel) (`level-minus 1 ∷ [])

  @0 subtype-identity-system : is-identity-system {A = Subtype ℓ T} Code (λ _ → idₑ , refl)
  subtype-identity-system = set-identity-system code-is-prop go where
    go : {U V : Subtype ℓ T} → Code U V → U ＝ V
    go {V = _ , g , _} (e , p) = Σ-pathP (ua e) $ to-pathP⁻ $ Σ-prop-path! $ p ∙ fun-ext λ x →
       ap g (sym (ua-β e x)) ∙ sym (transport-refl _)
