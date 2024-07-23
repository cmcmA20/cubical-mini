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

open import Data.Bool.Base
open import Data.Dec
open import Data.Empty.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Term

record DecProp (ℓ : Level) : Type (ℓsuc ℓ) where
  constructor el
  field
    carrier         : Type ℓ
    carrier-is-dec  : Dec carrier
    carrier-is-prop : is-prop carrier

open DecProp

unquoteDecl DecProp-iso = declare-record-iso DecProp-iso (quote DecProp)

private variable
  ℓ ℓ′ ℓ″ : Level

instance
  Underlying-DecProp : Underlying (DecProp ℓ)
  Underlying-DecProp {ℓ} .ℓ-underlying = ℓ
  Underlying-DecProp .⌞_⌟⁰ = carrier

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
dec-prop≃ᴱbool .snd = is-isoᴱ→is-equivᴱ go where
  go : is-isoᴱ (⌊_⌋ ∘ carrier-is-dec )
  go .fst false = el (Lift _ ⊥) auto (hlevel 1)
  go .fst true  = el (Lift _ ⊤) auto (hlevel 1)
  go .snd .fst .erased false = refl
  go .snd .fst .erased true  = refl
  go .snd .snd .erased (el A (no ¬a) _) = ext ((λ ())    , λ a → lift (¬a a))
  go .snd .snd .erased (el A (yes a) _) = ext ((λ _ → a) , λ _ → lift tt)
