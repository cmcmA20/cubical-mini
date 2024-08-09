{-# OPTIONS --safe --no-exact-split #-}
module Data.Maybe.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  x y : A
  b : Bool

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
  Code-Maybe nothing  nothing  = ⊤
  Code-Maybe _ _ = ⊥

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
  H-Level-Maybe : ∀ {ℓ} {A : Type ℓ} {n} → ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level n A ⦄ → H-Level n (Maybe A)
  H-Level-Maybe {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = maybe-is-of-hlevel _ (hlevel n)
  {-# OVERLAPS H-Level-Maybe #-}

instance
  Reflects-just≠nothing : Reflects (just x ＝ nothing) false
  Reflects-just≠nothing = ofⁿ (λ p → ¬-so-false (subst So (ap is-just? p) oh))

  Reflects-nothing≠just : Reflects (nothing ＝ just x) false
  Reflects-nothing≠just = ofⁿ (λ p → ¬-so-false (subst So (ap is-nothing? p) oh))

  Reflects-just=just : ⦃ Reflects (x ＝ y) b ⦄ → Reflects (just x ＝ just y) b
  Reflects-just=just = Reflects.dmap (ap just) (contra just-inj) auto

  Maybe-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Maybe A)
  Maybe-is-discrete {x = nothing} {(nothing)} = true   because auto
  Maybe-is-discrete {x = just _}  {(nothing)} = false  because auto
  Maybe-is-discrete {x = nothing} {just _}    = false  because auto
  Maybe-is-discrete {x = just x}  {just y}    = x =? y because auto

opaque
  nothing≠just : nothing ≠ just x
  nothing≠just = false!

opaque
  just≠nothing : just x ≠ nothing
  just≠nothing = false!
