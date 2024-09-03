{-# OPTIONS --safe --no-exact-split #-}
module Structures.DecProp where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Record
open import Meta.Projection
open import Meta.Reflection.Base

open import Structures.n-Type

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Bool.Base as Bool
open import Data.Dec as Dec
open import Data.Empty.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Term
open import Data.Truncation.Propositional.Base
open import Data.Unit.Base

record DecProp (ℓ : Level) : Type (ℓsuc ℓ) where
  constructor el
  field
    carrier         : Type ℓ
    carrier-is-dec  : Decidable carrier
    carrier-is-prop : is-prop carrier

open DecProp

unquoteDecl DecProp-iso = declare-record-iso DecProp-iso (quote DecProp)

private variable
  ℓ ℓ′ ℓ″ : Level

instance
  Underlying-DecProp : Underlying (DecProp ℓ)
  Underlying-DecProp {ℓ} .ℓ-underlying = ℓ
  Underlying-DecProp .⌞_⌟ = carrier

  hlevel-proj-DecProp : Struct-proj-desc true (quote carrier)
  hlevel-proj-DecProp .Struct-proj-desc.has-level = quote carrier-is-prop
  hlevel-proj-DecProp .Struct-proj-desc.get-level _ = pure (lit (nat 1))
  hlevel-proj-DecProp .Struct-proj-desc.upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-DecProp .Struct-proj-desc.get-argument (_ ∷ x v∷ []) = pure x
  hlevel-proj-DecProp .Struct-proj-desc.get-argument _ = type-error []

  ×-DecProp : ×-notation (DecProp ℓ) (DecProp ℓ′) _
  ×-DecProp ._×_ (el A da p) (el B db q) =
    el (A × B) (da <,> db) (×-is-of-hlevel 1 p q)

  ⇒-DecProp : ⇒-notation (DecProp ℓ) (DecProp ℓ′) _
  ⇒-DecProp ._⇒_ (el A da _) (el B db q) =
    el (A ⇒ B) (Dec-fun ⦃ da ⦄ ⦃ db ⦄) (fun-is-of-hlevel 1 q)

  ⊎₁-DecProp : ⊎₁-notation (DecProp ℓ) (DecProp ℓ′) (DecProp (ℓ ⊔ ℓ′))
  ⊎₁-DecProp ._⊎₁_ (el A da p) (el B db q) =
    el (A ⊎₁ B) (∥-∥₁∘dec≃dec∘∥-∥₁ $ ∣ da <+> db ∣₁) squash₁

  ¬-DecProp : ¬-notation (DecProp ℓ) (DecProp ℓ)
  ¬-DecProp .¬_ (el A da p) = el (¬ A) (Dec-¬ ⦃ da ⦄) (hlevel 1)

  Σ-DecProp : Σ-notation (DecProp ℓ) (DecProp ℓ′) (DecProp (ℓ ⊔ ℓ′))
  Σ-DecProp .Σ-notation.Σ (el A da p) F =
    el (Σ[ a ꞉ A ] ⌞ F a ⌟)
       (Dec-prop-Σ p da (λ {x} → F x .carrier-is-dec))
       (Σ-is-of-hlevel 1 p (λ x → F x .carrier-is-prop))

  ⊥-DecProp-small : ⊥-notation (DecProp 0ℓ)
  ⊥-DecProp-small .⊥ = el ⊥ auto (hlevel 1)
  {-# OVERLAPPING ⊥-DecProp-small #-}

  ⊥-DecProp : ⊥-notation (DecProp ℓ)
  ⊥-DecProp .⊥ = el ⊥ auto (hlevel 1)
  {-# INCOHERENT ⊥-DecProp #-}

  ⊤-DecProp-small : ⊤-notation (DecProp 0ℓ)
  ⊤-DecProp-small .⊤ = el ⊤ auto (hlevel 1)
  {-# OVERLAPPING ⊤-DecProp-small #-}

  ⊤-DecProp : ⊤-notation (DecProp ℓ)
  ⊤-DecProp .⊤ = el ⊤ auto (hlevel 1)
  {-# OVERLAPPABLE ⊤-DecProp #-}

  @0 Extensional-DecProp : Extensional (DecProp ℓ) ℓ
  Extensional-DecProp .Pathᵉ (el A da p) (el B db q) = (A → B) × (B → A)
  Extensional-DecProp .reflᵉ _ = refl , refl
  Extensional-DecProp .idsᵉ .to-path {a = el A da p} {b = el B db q} (f , g) =
    Equiv.injective (≅→≃ DecProp-iso) (ua (prop-extₑ! f g) ,ₚ prop!)
    where instance _ = hlevel-prop-instance p
                   _ = hlevel-prop-instance q
  Extensional-DecProp .idsᵉ .to-path-over {a = el _ _ p} _ = prop!
    where instance _ = hlevel-prop-instance p

dec-prop≃ᴱbool : DecProp ℓ ≃ᴱ Bool
dec-prop≃ᴱbool .fst X = ⌊ X .carrier-is-dec ⌋
dec-prop≃ᴱbool .snd = is-invᴱ→is-equivᴱ
  $ (if_then ⊤-DecProp .⊤ else ⊥-DecProp .⊥)
  , erase (fun-ext (Bool.elim refl refl))
  , erase (fun-ext li)
  where
  @0 li : _
  li (el A (no ¬a) z) = ext ((λ ())    , lift ∘ ¬a)
  li (el A (yes a) z) = ext ((λ _ → a) , λ _ → lift tt)
