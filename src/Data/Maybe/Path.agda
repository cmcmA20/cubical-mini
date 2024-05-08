{-# OPTIONS --safe #-}
module Data.Maybe.Path where

open import Meta.Prelude

open import Meta.Extensionality

open import Functions.Embedding

open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Unit.Base

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  x y : A

nothing≠just : nothing ≠ just x
nothing≠just p = subst is-nothing p tt

just≠nothing : just x ≠ nothing
just≠nothing = nothing≠just ∘ symₚ

just-inj : just x ＝ just y → x ＝ y
just-inj {x} = ap (from-just x)

¬→maybe-is-contr : (¬ A) → is-contr (Maybe A)
¬→maybe-is-contr ¬a = inhabited-prop-is-contr nothing λ where
  nothing  nothing  → refl
  nothing  (just a) → ⊥.rec $ ¬a a
  (just a) _        → ⊥.rec $ ¬a a


module _ ⦃ sa : Extensional A ℓ ⦄ where
  Code-Maybe : Maybe A → Maybe A → Type ℓ
  Code-Maybe (just x) (just y) = sa .Pathᵉ x y
  Code-Maybe nothing  nothing  = Lift _ ⊤
  Code-Maybe _ _ = Lift _ ⊥

  instance
    Extensional-Maybe : Extensional (Maybe A) ℓ
    Extensional-Maybe .Pathᵉ = Code-Maybe
    Extensional-Maybe .reflᵉ (just x) = sa .reflᵉ x
    Extensional-Maybe .reflᵉ nothing  = _
    Extensional-Maybe .idsᵉ .to-path {just x}    {just _}      = ap just ∘ sa .idsᵉ .to-path
    Extensional-Maybe .idsᵉ .to-path {(nothing)} {(nothing)} c = refl
    Extensional-Maybe .idsᵉ .to-path-over {just _}    {just _}      = sa .idsᵉ .to-path-over
    Extensional-Maybe .idsᵉ .to-path-over {(nothing)} {(nothing)} _ = refl

opaque
  code-maybe-is-of-hlevel : {x y : Maybe A} {n : HLevel}
                          → is-of-hlevel (2 + n) A
                          → is-of-hlevel (1 + n) (Code-Maybe x y)
  code-maybe-is-of-hlevel {x = just x}  {just y}    hl = path-is-of-hlevel _ hl x y
  code-maybe-is-of-hlevel {x = nothing} {(nothing)} _  = hlevel _
  code-maybe-is-of-hlevel {x = just x}  {(nothing)} _ = hlevel _
  code-maybe-is-of-hlevel {x = nothing} {just x}    _ = hlevel _

  maybe-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) A → is-of-hlevel (2 + n) (Maybe A)
  maybe-is-of-hlevel n hl =
    identity-system→is-of-hlevel _ (Extensional-Maybe .idsᵉ) λ x y → code-maybe-is-of-hlevel {x = x} hl


just-cancellable : Cancellable {A = A} just
just-cancellable = identity-system-gives-path (Extensional-Maybe .idsᵉ) ⁻¹

just-is-embedding : is-embedding {A = A} just
just-is-embedding = cancellable→is-embedding just-cancellable

instance opaque
  H-Level-Maybe : ∀ {n ℓ} {A : Type ℓ} → ⦃ A-hl : H-Level (2 + n) A ⦄ → H-Level (2 + n) (Maybe A)
  H-Level-Maybe {n} .H-Level.has-of-hlevel = maybe-is-of-hlevel _ (hlevel (2 + n))
