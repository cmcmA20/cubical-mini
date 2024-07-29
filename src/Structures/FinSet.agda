{-# OPTIONS --safe --no-exact-split #-}
module Structures.FinSet where

open import Meta.Prelude
open import Meta.Effect.Bind
open import Meta.Projection
open import Meta.Record
open import Meta.Reflection.Base
open import Meta.SIP

open import Structures.n-Type

open import Logic.Discreteness

open import Combinatorics.Finiteness.Bishop.Weak

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Term
open import Data.Truncation.Propositional as ∥-∥₁
open import Data.Truncation.Set as ∥-∥₂

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ

record FinSet (ℓ : Level) : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-set
  field
    carrier : Type ℓ
    has-bishop-finite : is-bishop-finite carrier

  fin-set-carrier-is-set : is-set carrier
  fin-set-carrier-is-set = is-discrete→is-set (is-bishop-finite→is-discrete ⦃ has-bishop-finite ⦄)

open FinSet

unquoteDecl fin-set-iso = declare-record-iso fin-set-iso (quote FinSet)

instance
  Underlying-FinSet : Underlying (FinSet ℓ)
  Underlying-FinSet {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinSet .⌞_⌟ = carrier

  bf-proj-fin-ord : Struct-proj-desc false (quote carrier)
  bf-proj-fin-ord .Struct-proj-desc.has-level = quote has-bishop-finite
  bf-proj-fin-ord .Struct-proj-desc.get-argument (_ ∷ x v∷ []) = pure x
  bf-proj-fin-ord .Struct-proj-desc.get-argument _ = type-error []

  bf-projection
    : ∀ {ℓ} {A : Type ℓ}
    → {@(tactic struct-proj A nothing) A-bf : is-bishop-finite A}
    → is-bishop-finite A
  bf-projection {A-bf} = A-bf
  {-# OVERLAPS bf-projection #-}

  hlevel-proj-fin-ord : Struct-proj-desc true (quote carrier)
  hlevel-proj-fin-ord .Struct-proj-desc.has-level = quote fin-set-carrier-is-set
  hlevel-proj-fin-ord .Struct-proj-desc.get-level _ = pure (lit (nat 2))
  hlevel-proj-fin-ord .Struct-proj-desc.upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-fin-ord .Struct-proj-desc.get-argument (_ ∷ x v∷ []) = pure x
  hlevel-proj-fin-ord .Struct-proj-desc.get-argument _ = type-error []

  ×-FinSet : ×-notation (FinSet ℓ) (FinSet ℓ′) (FinSet (ℓ ⊔ ℓ′))
  ×-FinSet ._×_ X Y .carrier = ⌞ X ⌟ × ⌞ Y ⌟
  ×-FinSet ._×_ _ _ .has-bishop-finite = auto

  ⇒-FinSet : ⇒-notation (FinSet ℓ) (FinSet ℓ′) (FinSet (ℓ ⊔ ℓ′))
  ⇒-FinSet ._⇒_ X Y .carrier = ⌞ X ⌟ ⇒ ⌞ Y ⌟
  ⇒-FinSet ._⇒_ _ _ .has-bishop-finite = auto

  Π-FinSet : Π-notation (FinSet ℓ) (FinSet ℓ′) (FinSet (ℓ ⊔ ℓ′))
  Π-FinSet .Π-notation.Π A F .carrier = Π[ a ꞉ ⌞ A ⌟ ] ⌞ F a ⌟
  Π-FinSet .Π-notation.Π _ _ .has-bishop-finite = auto

  ∀-FinSet : ∀-notation (FinSet ℓ) (FinSet ℓ′) (FinSet (ℓ ⊔ ℓ′))
  ∀-FinSet .∀-notation.∀′ A F .carrier = ∀[ a ꞉ ⌞ A ⌟ ] ⌞ F a ⌟
  ∀-FinSet .∀-notation.∀′ X F .has-bishop-finite = ≃→is-bishop-finite (Π≃∀ ⁻¹)
    (Π-is-bishop-finite ⦃ X .has-bishop-finite ⦄ ⦃ λ {x} → F x .has-bishop-finite ⦄ )

  Σ-FinSet : Σ-notation (FinSet ℓ) (FinSet ℓ′) (FinSet (ℓ ⊔ ℓ′))
  Σ-FinSet .Σ-notation.Σ A F .carrier = Σ[ a ꞉ ⌞ A ⌟ ] ⌞ F a ⌟
  Σ-FinSet .Σ-notation.Σ _ _ .has-bishop-finite = auto


@0 FinSet-is-groupoid : is-groupoid (FinSet ℓ)
FinSet-is-groupoid = ≃→is-of-hlevel! 3 go where
  go = FinSet _
         ~⟨ ≅→≃ fin-set-iso ⟩
       Σ[ X ꞉ Type _ ] is-bishop-finite X
         ~⟨ Σ-ap-snd (λ _ → prop-extₑ! < (λ bf → is-discrete→is-set (is-bishop-finite→is-discrete ⦃ bf ⦄)) , id > snd) ⟩
       Σ[ X ꞉ Type _ ] is-set X × is-bishop-finite X
         ~⟨ Σ-assoc ⟩
       Σ[ U ꞉ Σ[ X ꞉ Type _ ] is-set X ] is-bishop-finite (U .fst)
         ~⟨ Σ-ap-fst (≅→≃ n-Type-iso) ⟨
       Σ[ X ꞉ Set _ ] is-bishop-finite ⌞ X ⌟
         ∎

instance
  @0 H-Level-FinSet : ∀ {n} → ⦃ n ≥ʰ 3 ⦄ → H-Level n (FinSet ℓ)
  H-Level-FinSet ⦃ s≤ʰs (s≤ʰs (s≤ʰs _)) ⦄ = hlevel-basic-instance 3 FinSet-is-groupoid
  {-# OVERLAPPING H-Level-FinSet #-}


-- have to go through sigmas
private
  fin-set′-desc : Desc ℓ _ (λ X → ℕ) ℓ
  fin-set′-desc .Desc.descriptor = auto-str-term!
  fin-set′-desc .Desc.axioms X n = ∥ X ≃ Fin n ∥₁
  fin-set′-desc .Desc.axioms-prop = hlevel!

  fin-set′-str : Structure {ℓ₁ = ℓ} 0ℓ _
  fin-set′-str = desc→structure fin-set′-desc

  @0 fin-set-str-is-univalent : is-univalent {_} {ℓ} fin-set′-str
  fin-set-str-is-univalent = desc→is-univalent fin-set′-desc

  FinSet′ : (ℓ : Level) → Type (ℓsuc ℓ)
  FinSet′ _ = Type-with fin-set′-str

  @0 fin-set′-ext : {X Y : FinSet′ ℓ} → (X .snd .fst ＝ Y .snd .fst) → ∥ X ＝ Y ∥₁
  fin-set′-ext {X} {Y} p = do
    u ← X .snd .snd
    v ← Y .snd .snd
    pure $ sip fin-set-str-is-univalent (u ∙ =→≃ (ap (λ n → Fin n) p) ∙ v ⁻¹ , p)

  ∥FinSet′∥₂≃ᴱℕ : ∥ FinSet′ ℓ ∥₂ ≃ᴱ ℕ
  ∥FinSet′∥₂≃ᴱℕ {ℓ} = rec! ⦃ Inductive-∥-∥₂ ⦃ Inductive-default ⦄ ⦄ (fst ∘ snd) , is-isoᴱ→is-equivᴱ {B = ℕ}
    ( (λ n → pure $ Lift ℓ (Fin n) , n , pure lift≃id)
    , erase (λ _ → refl)
    , erase (elim! λ X n e → =∘∣-∣₂≃∥-∥₁∘= ⁻¹ $ fin-set′-ext refl) )

∥FinSet∥₂≃ᴱℕ : ∥ FinSet ℓ ∥₂ ≃ᴱ ℕ
∥FinSet∥₂≃ᴱℕ {ℓ} =
  ∥ FinSet  ℓ ∥₂  ~⟨ ≃→≃ᴱ (∥-∥₂.ae (≅→≃ fin-set-iso ∙ Σ-ap-snd λ _ → ≅→≃ is-bishop-finite-iso)) ⟩
  ∥ FinSet′ ℓ ∥₂  ~⟨ ∥FinSet′∥₂≃ᴱℕ ⟩
  ℕ               ∎


-- Usage
module _ {ℓᵃ ℓᵇ : Level} {A : FinSet ℓᵃ} {B : ⌞ A ⌟ ⇒ FinSet ℓᵇ} where private
  open import Logic.Exhaustibility
  open import Logic.Omniscience

  _ : is-groupoid ⌞ A ⇒ A ⌟
  _ = hlevel!

  _ : is-discrete ⌞ A × A ⌟
  _ = auto

  _ : is-bishop-finite (⌞ A ⌟ ⇒ ⌞ A ⇒ A ⌟)
  _ = auto

  _ : Omniscient₁ ⌞ Π[ B ] ⌟
  _ = autoω

  _ : Exhaustible ⌞ A × A ⌟
  _ = autoω

  _ : {x y : ⌞ A ⌟} → is-bishop-finite (x ＝ y)
  _ = auto
