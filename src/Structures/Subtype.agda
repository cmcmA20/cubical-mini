{-# OPTIONS --safe #-}
module Structures.Subtype where

open import Foundations.Base
open import Foundations.Pi
open import Foundations.Sigma

open import Meta.Extensionality
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
  n : HLevel

Subtype : (ℓ : Level) → Type ℓ → Type _
Subtype ℓ T = Σ[ X ꞉ Type ℓ ] X ↪ T

@0 subtype≃ℙ : Subtype ℓ T ≃ ℙ T
subtype≃ℙ = subtype-classifier ∙ₑ Π-cod-≃ λ _ → iso→equiv n-Type-iso ₑ⁻¹

@0 subtype-is-set : is-set (Subtype ℓ T)
subtype-is-set = is-of-hlevel-≃ 2 subtype≃ℙ hlevel!

instance
  @0 H-Level-subtype : H-Level (2 + n) (Subtype ℓ T)
  H-Level-subtype = hlevel-basic-instance 2 subtype-is-set

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

  @0 identity-system : is-identity-system {A = Subtype ℓ T} Code (λ _ → idₑ , refl)
  identity-system = set-identity-system code-is-prop go where
    go : {U V : Subtype ℓ T} → Code U V → U ＝ V
    go {V = _ , g , _} (e , p) = Σ-pathP (ua e) $ to-pathP⁻ $ Σ-prop-path! $ p ∙ fun-ext λ x →
       ap g (sym (ua-β e x)) ∙ sym (transport-refl _)


@0 Extensional-Subtype : Extensional (Subtype ℓ T) ℓ
Extensional-Subtype .Pathᵉ = Path.Code
Extensional-Subtype .reflᵉ _ = idₑ , refl
Extensional-Subtype .idsᵉ = Path.identity-system

instance
  extensionality-subtype : Extensionality (Subtype ℓ T)
  extensionality-subtype .Extensionality.lemma = quote Extensional-Subtype
