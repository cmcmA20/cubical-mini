{-# OPTIONS --safe #-}
module Meta.Groupoid where

open import Foundations.Base renaming (_∙_ to _∙ₚ_; _∘′_ to _∘′ₜ_)
open import Foundations.Equiv
open import Foundations.Erased

open import Meta.Effect.Alt
open import Meta.Reflection.Base

open import Data.List.Base
open import Data.List.Instances.FromProduct

data Size : 𝒰 where
  small large : Size

-- TODO abstract again for use with categories
Relₛ² : Size → 𝒰ω
Relₛ² small = ∀{ℓ} {A : 𝒰 ℓ} → A    → A     → 𝒰 ℓ
Relₛ² large = ∀{ℓ ℓ′}         → 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)

Neutralₛ : (s : Size) → Relₛ² s → 𝒰ω
Neutralₛ small _~_ = ∀ {ℓ} {A : 𝒰 ℓ} {x : A}    → x ~ x
Neutralₛ large _~_ = ∀ {ℓ}            {A : 𝒰 ℓ} → A ~ A

-- `ₐ` for automatic? FIXME naming

record Refl (s : Size) (_~_ : Relₛ² s) : 𝒰ω where
  no-eta-equality
  field reflₐ : Neutralₛ s _~_

open Refl ⦃ ... ⦄ public

instance
  Refl-path : Refl small _＝_
  Refl-path .reflₐ = refl

  Refl-Fun : Refl large (λ {ℓ} {ℓ′} (A : 𝒰 ℓ) (B : 𝒰 ℓ′) → A → B)
  Refl-Fun .reflₐ = id

  Refl-≃ : Refl large _≃_
  Refl-≃ .reflₐ = idₑ

  Refl-≃ᴱ : Refl large _≃ᴱ_
  Refl-≃ᴱ .reflₐ = ≃→≃ᴱ idₑ

  Refl-iso : Refl large _≅_
  Refl-iso .reflₐ = idᵢ

try-sized : Term → Name → Term → TC ⊤
try-sized s r hole = do
  (mv , sol) ← new-meta′ (def (quote Refl) (s v∷ def r [] v∷ []))
  (`cmp ∷ _) ← get-instances mv
    where _ → type-error [ "No (or too many) instances" ]
  unify sol `cmp
  unify hole $ (def (quote reflₐ) $ s h∷ def r [] h∷ sol i∷ [] )

private
  refl-macro : Term → TC ⊤
  refl-macro hole = do
    ty ← (infer-type hole) >>= wait-just-a-bit
    debug-print "tactic.id" 20 [ "Goal: " , termErr ty ]
    def r (_ h∷ _ h∷ _ v∷ _ v∷ []) ← pure ty
      where t → type-error [ "Target is not an application of a binary relation: " , termErr t ]
    try-sized (con (quote small) []) r hole <|> try-sized (con (quote large) []) r hole

macro refl! = refl-macro


Concatₛ : (s : Size) → Relₛ² s → 𝒰ω
Concatₛ small _~_ = ∀ {ℓ} {A : 𝒰 ℓ} {x y z : A}                        → x ~ y → y ~ z → x ~ z
Concatₛ large _~_ = ∀ {ℓ ℓ′ ℓ″}      {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {C : 𝒰 ℓ″} → A ~ B → B ~ C → A ~ C

Concat⁻ₛ : (s : Size) → Relₛ² s → 𝒰ω
Concat⁻ₛ small _~_ = ∀ {ℓ} {A : 𝒰 ℓ} {x y z : A}                        → y ~ z → x ~ y → x ~ z
Concat⁻ₛ large _~_ = ∀ {ℓ ℓ′ ℓ″}      {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {C : 𝒰 ℓ″} → B ~ C → A ~ B → A ~ C

private
  flipₛ : (s : Size) {r : Relₛ² s} → Concatₛ s r → Concat⁻ₛ s r
  flipₛ small = λ f p q → f q p
  flipₛ large = λ f p q → f q p

record Compose (s : Size) (_~_ : Relₛ² s) : 𝒰ω where
  no-eta-equality
  infixr 30 _∙_
  field _∙_ : Concatₛ s _~_

  infixr 9 _∘′_
  _∘′_ : Concat⁻ₛ s _~_
  _∘′_ = flipₛ _ _∙_

open Compose ⦃ ... ⦄ public

instance
  Compose-path : Compose small _＝_
  Compose-path ._∙_  = _∙ₚ_

  Compose-Fun : Compose large (λ {ℓ} {ℓ′} (A : 𝒰 ℓ) (B : 𝒰 ℓ′) → A → B)
  Compose-Fun ._∙_ f g = g ∘′ₜ f

  Compose-≃ : Compose large _≃_
  Compose-≃ ._∙_  = _∙ₑ_

  Compose-≃ᴱ : Compose large _≃ᴱ_
  Compose-≃ᴱ ._∙_  = _∙ᴱₑ_

  Compose-iso : Compose large _≅_
  Compose-iso ._∙_  = _∙ᵢ_


Inverseₛ : (s : Size) → Relₛ² s → 𝒰ω
Inverseₛ small _~_ = ∀ {ℓ} {A : 𝒰 ℓ} {x y : A}      → x ~ y → y ~ x
Inverseₛ large _~_ = ∀ {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} → A ~ B → B ~ A

record Invertible (s : Size) (_~_ : Relₛ² s) : 𝒰ω where
  no-eta-equality
  infix 90 _⁻¹
  field _⁻¹  : Inverseₛ  s _~_

open Invertible ⦃ ... ⦄ public

instance
  Inv-path : Invertible small _＝_
  Inv-path ._⁻¹ = sym

  Inv-≃ : Invertible large _≃_
  Inv-≃ ._⁻¹ = _ₑ⁻¹

  Inv-≃ᴱ : Invertible large _≃ᴱ_
  Inv-≃ᴱ ._⁻¹ = _ᴱₑ⁻¹

  Inv-iso : Invertible large _≅_
  Inv-iso ._⁻¹ = _ᵢ⁻¹
