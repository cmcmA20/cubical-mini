{-# OPTIONS --safe #-}
module Data.Maybe.Path where

open import Meta.Prelude

open import Structures.IdentitySystem
open import Structures.n-Type

open import Functions.Embedding

open import Data.Empty.Base
open import Data.Unit.Base

open import Data.Maybe.Base

private variable
  ℓ : Level
  A : Type ℓ
  x y : A

Code : Maybe A → Maybe A → Type _
Code (just x) (just y) = x ＝ y
Code nothing  nothing  = Lift _ ⊤
Code _        _        = Lift _ ⊥

code-refl : (x : Maybe A) → Code x x
code-refl (just _) = refl
code-refl nothing  = _

identity-system : is-identity-system {A = Maybe A} Code code-refl
identity-system .to-path {just x}    {just y}    c = ap just c
identity-system .to-path {(nothing)} {(nothing)} _ = refl
identity-system .to-path-over {just x}    {just y}    p i j = p (i ∧ j)
identity-system .to-path-over {(nothing)} {(nothing)} _ = refl

code-is-of-hlevel : {x y : Maybe A} {n : HLevel}
                  → is-of-hlevel (2 + n) A
                  → is-of-hlevel (1 + n) (Code x y)
code-is-of-hlevel {x = just x}  {just y}    A-hl = path-is-of-hlevel _ A-hl x y
code-is-of-hlevel {x = nothing} {(nothing)} _    = hlevel!
code-is-of-hlevel {x = just x}  {(nothing)} _    = hlevel!
code-is-of-hlevel {x = nothing} {just x}    _    = hlevel!

maybe-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) A → is-of-hlevel (2 + n) (Maybe A)
maybe-is-of-hlevel n A-hl =
  identity-system→is-of-hlevel _ identity-system λ _ _ → code-is-of-hlevel A-hl

nothing≠just : nothing ≠ just x
nothing≠just p = subst is-nothing p tt

just≠nothing : just x ≠ nothing
just≠nothing = nothing≠just ∘ symₚ

just-inj : just x ＝ just y → x ＝ y
just-inj {x} = ap (from-just x)

just-cancellable : Cancellable {A = A} just
just-cancellable = identity-system-gives-path identity-system ⁻¹

just-is-embedding : is-embedding {A = A} just
just-is-embedding = cancellable→is-embedding just-cancellable

instance
  H-Level-Maybe : ∀ {n ℓ} {A : Type ℓ} → ⦃ A-hl : H-Level (2 + n) A ⦄ → H-Level (2 + n) (Maybe A)
  H-Level-Maybe .H-Level.has-of-hlevel = maybe-is-of-hlevel _ hlevel!
