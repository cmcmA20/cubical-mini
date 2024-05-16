{-# OPTIONS --safe #-}
module Combinatorics.Finiteness.Listed where

open import Meta.Prelude

open import Meta.Marker
open import Meta.Membership
open import Meta.Record

open import Logic.Discreteness

open import Combinatorics.Finiteness.ManifestBishop

open import Functions.Embedding

open import Data.Dec.Base
open import Data.Empty.Base as ⊥
open import Data.Dec.Properties
open import Data.Fin.Computational.Base as Fin
open import Data.Fin.Computational.Instances.Discrete
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Path
open import Data.List.Membership

record Listed {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor finₗ
  field
    support : List A
    cover   : Π[ x ꞉ A ] x ∈! support

open Listed public

unquoteDecl Listed-iso = declare-record-iso Listed-iso (quote Listed)

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ
  n : HLevel

instance
  H-Level-Listed : ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level n A ⦄ → H-Level n (Listed A)
  H-Level-Listed {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = ≅→is-of-hlevel n Listed-iso (hlevel n)

listed→Σ∈!-is-discrete : (lis : Listed A) → is-discrete (Σ[ x ꞉ A ] x ∈! lis .support)
listed→Σ∈!-is-discrete lis {a₁ , a₁∈l , u} {a₂ , a₂∈l , v} = caseᵈ ∈ₗ→fin a₁∈l ＝ ∈ₗ→fin a₂∈l of λ where
  (yes p=q) → yes (∈ₗ→fin-almost-injective a₁∈l a₂∈l p=q ,ₚ prop!)
  (no  p≠q) → no λ x → p≠q (∈ₗ→fin-respects-∈!ₗ a₁∈l u a₂∈l v (ap fst x))

listed-embedding : (lis : Listed A) → A ↪ (Σ[ x ꞉ A ] x ∈! lis .support)
listed-embedding lis .fst a = a , lis .cover a
listed-embedding lis .snd (c , c∈l , u) (a , p) (b , q)
  =  ap fst (p ∙ q ⁻¹)
  ,ₚ Σ-prop-square! (commutes→square lemma)
  where
  lemma : ap fst (p ∙ q ⁻¹) ∙ ap fst q ＝ ap fst p ∙ refl
  lemma =
    ⌜ ap fst (p ∙ q ⁻¹) ⌝ ∙ ap fst q       ~⟨ ap! (ap-comp-∙ fst p _) ⟩
    (ap fst p ∙ ap fst (q ⁻¹)) ∙ ap fst q  ~⟨ ∙-cancel-r _ _ ⟩
    ap fst p                               ~⟨ ∙-id-r _ ⟨
    ap fst p ∙ refl                        ∎

listed→is-discrete : Listed A → is-discrete A
listed→is-discrete lis = ↪→is-discrete (listed-embedding lis) (listed→Σ∈!-is-discrete lis)
