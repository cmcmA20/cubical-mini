{-# OPTIONS --safe #-}
module Structures.Subtype where

open import Meta.Prelude

open import Meta.Extensionality
open import Meta.Membership
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

-- TODO refactor as a record
Subtype : (ℓ : Level) → Type ℓ → Type _
Subtype ℓ T = Σ[ X ꞉ Type ℓ ] X ↪ T

@0 subtype≃ℙ : Subtype ℓ T ≃ ℙ T
subtype≃ℙ = subtype-classifier ∙ Π-cod-≃ λ _ → iso→equiv n-Type-iso ⁻¹

@0 subtype-is-set : is-set (Subtype ℓ T)
subtype-is-set = is-of-hlevel-≃ 2 subtype≃ℙ hlevel!

instance
  @0 H-Level-subtype : H-Level (2 + n) (Subtype ℓ T)
  H-Level-subtype = hlevel-basic-instance 2 subtype-is-set

module Path where

  Code : Subtype ℓ T → Subtype ℓ T → Type _
  Code (X , f , _) (Y , g , _) = Σ[ e ꞉ X ≃ Y ] Π[ x ꞉ X ] (f x ＝ g (e $ x))

  @0 code≃path : (U V : Subtype ℓ T) → Code U V ≃ (U ＝ V)
  code≃path U@(X , f , f-emb) V@(Y , g , g-emb) =
    Code U V                                      ≃⟨⟩
    Σ[ e ꞉ X ≃ Y ] Π[ x ꞉ X ] (f x ＝ g (e $ x))  ≃⟨ SIP (fibration-str-is-univalent _ _) ⟩
    (X , f) ＝ (Y , g)                            ≃⟨ Σ-prop-path-≃ hlevel! ⟩
    ((X , f) , f-emb) ＝ ((Y , g) , g-emb)        ≃˘⟨ ap-≃ Σ-assoc ⟩
    U ＝ V                                        ≃∎

  @0 code-is-prop : (U V : Subtype ℓ T) → is-prop (Code U V)
  code-is-prop U V = is-of-hlevel-≃ 1 (code≃path U V) (path-is-of-hlevel′ 1 subtype-is-set U V)

  @0 identity-system : ∀{ℓ} {T : 𝒰 ℓ} → is-identity-system {A = Subtype ℓ T} Code (λ _ → refl , λ _ → refl)
  identity-system = set-identity-system code-is-prop go where
    go : {U V : Subtype ℓ T} → Code U V → U ＝ V
    go {V = _ , g , _} (e , p)
      =  ua e
      ,ₚ to-pathP⁻ (Σ-prop-path! $ fun-ext λ x → p x ∙ (transport-refl _ ∙ ap g (ua-β e x)) ⁻¹)


@0 Extensional-Subtype : Extensional (Subtype ℓ T) ℓ
Extensional-Subtype .Pathᵉ = Path.Code
Extensional-Subtype .reflᵉ _ = refl , λ _ → refl
Extensional-Subtype .idsᵉ = Path.identity-system

instance
  extensionality-subtype : Extensionality (Subtype ℓ T)
  extensionality-subtype .Extensionality.lemma = quote Extensional-Subtype

  membership-subtype : ∀{ℓ} {A : Type ℓ} → Membership A (Subtype ℓ A) ℓ
  membership-subtype .Membership._∈_ x (A′ , e) = fibre {A = A′} (e $_) x

opaque
  unfolding is-of-hlevel
  subtype-membership-is-prop
    : ∀ {ℓ} {A : Type ℓ} {P : Subtype ℓ A} {x : A} → is-prop (x ∈ P)
  subtype-membership-is-prop {P = A′ , e} {x} = e .snd x
