{-# OPTIONS --safe #-}
module Meta.Groupoid where

open import Foundations.Prelude
  renaming ( _∙_  to _∙ₚ_
           ; _∘ˢ_ to _∘ₜˢ_
           ; refl to reflₚ
           ; sym  to symₚ
           )

open import Meta.Effect.Alt
open import Meta.Reflection.Base
open import Meta.Reflection.Signature

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Maybe.Base

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
  field refl′ : Neutralₛ s _~_

open Refl ⦃ ... ⦄ public

instance
  Refl-path : Refl small _＝_
  Refl-path .refl′ = reflₚ

  Refl-Fun : Refl large Fun
  Refl-Fun .refl′ = id

  Refl-≃ : Refl large _≃_
  Refl-≃ .refl′ = idₑ

  -- FIXME
  Refl-≃ᴱ : Refl large _≃ᴱ_
  Refl-≃ᴱ .refl′ = ≃→≃ᴱ idₑ

  Refl-iso : Refl large Iso
  Refl-iso .refl′ = idᵢ

private

  try-sized : Term → Term → Term → TC ⊤
  try-sized s r hole = do
    (mv , sol) ← new-meta′ $ it Refl ##ₙ s ##ₙ r
    (`cmp ∷ _) ← get-instances mv
      where _ → type-error [ "No (or too many) instances" ]
    unify sol `cmp
    unify hole $ it refl′ ##ₕ s ##ₕ r ##ᵢ sol

  decompose-as-path : Term → TC Term
  decompose-as-path (def (quote Pathᴾ) (l h∷ T v∷ _ v∷ _ v∷ [])) = do
    pure $ it _＝_
  decompose-as-path (def (quote _＝_) (l h∷ T h∷ _ v∷ _ v∷ [])) = do
    pure $ it _＝_
  decompose-as-path t = type-error [ "Target is not a path: " , termErr t ]

  decompose-as-fun : Term → TC Term
  decompose-as-fun t@(pi (varg x) (abs _ _)) = do
    unify t $ it Fun ##ₙ x ##ₙ x
    pure $ it Fun
  decompose-as-fun t = type-error [ "Target is not a function: " , termErr t ]

  decompose-as-other : Term → TC Term
  decompose-as-other (def r (_ h∷ _ h∷ _ v∷ _ v∷ [])) = pure $ def r []
  decompose-as-other t =
    type-error [ "Target is not an application of a binary relation: " , termErr t ]

  refl-macro : Term → TC ⊤
  refl-macro hole = with-reduce-defs (false , [ quote _≃_ , quote Iso , quote _≅_ ]) do
    ty ← (infer-type hole >>= reduce) >>= wait-just-a-bit
    debug-print "tactic.groupoid" 20 [ "Goal: " , termErr ty ]
    r ← decompose-as-path ty <|> decompose-as-fun ty <|> decompose-as-other ty
    try-sized (it small) r hole <|> try-sized (it large) r hole

macro refl = refl-macro


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

  infixr 9 _∘ˢ_
  _∘ˢ_ : Concat⁻ₛ s _~_
  _∘ˢ_ = flipₛ _ _∙_

open Compose ⦃ ... ⦄ public

instance
  Compose-path : Compose small _＝_
  Compose-path ._∙_  = _∙ₚ_

  Compose-Fun : Compose large (λ {ℓ} {ℓ′} (A : 𝒰 ℓ) (B : 𝒰 ℓ′) → A → B)
  Compose-Fun ._∙_ f g = g ∘ₜˢ f

  Compose-≃ : Compose large _≃_
  Compose-≃ ._∙_  = _∙ₑ_

  Compose-≃ᴱ : Compose large _≃ᴱ_
  Compose-≃ᴱ ._∙_  = _∙ᴱₑ_

  Compose-iso : Compose large Iso
  Compose-iso ._∙_  = _∙ᵢ_


Inverseₛ : (s : Size) → Relₛ² s → 𝒰ω
Inverseₛ small _~_ = ∀ {ℓ} {A : 𝒰 ℓ} {x y : A}      → x ~ y → y ~ x
Inverseₛ large _~_ = ∀ {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} → A ~ B → B ~ A

record Invertible (s : Size) (_~_ : Relₛ² s) : 𝒰ω where
  no-eta-equality
  infix 90 _⁻¹
  field _⁻¹  : Inverseₛ  s _~_

  sym = _⁻¹

open Invertible ⦃ ... ⦄ public

instance
  Inv-path : Invertible small _＝_
  Inv-path ._⁻¹ = symₚ

  Inv-≃ : Invertible large _≃_
  Inv-≃ ._⁻¹ = _ₑ⁻¹

  Inv-≃ᴱ : Invertible large _≃ᴱ_
  Inv-≃ᴱ ._⁻¹ = _ᴱₑ⁻¹

  Inv-iso : Invertible large Iso
  Inv-iso ._⁻¹ = _ᵢ⁻¹
