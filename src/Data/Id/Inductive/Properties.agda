{-# OPTIONS --safe #-}
module Data.Id.Inductive.Properties where

open import Foundations.Prelude

open import Logic.Discreteness

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥

open import Data.Id.Inductive.Base

private variable
  ℓᵃ : Level
  A : Type ℓᵃ
  x y : A

Id-identity-system : is-identity-system (_＝ⁱ_ {A = A}) (λ _ → reflⁱ)
Id-identity-system .to-path      reflⁱ = refl
Id-identity-system .to-path-over reflⁱ = refl

Id≃path : (x ＝ⁱ y) ≃ (x ＝ y)
Id≃path = identity-system-gives-path Id-identity-system

module Id≃path {ℓ} {A : Type ℓ} = IdS (Id-identity-system {A = A})


is-contrⁱ→is-contr : is-contrⁱ A → is-contr A
is-contrⁱ→is-contr (centre , _) .fst = centre
is-contrⁱ→is-contr (_ , paths)  .snd = Id≃path.to ∘ paths

opaque
  is-propⁱ→is-prop : is-propⁱ A → is-prop A
  is-propⁱ→is-prop A-propⁱ x y = Id≃path.to (A-propⁱ x y)

  is-setⁱ→is-set : is-setⁱ A → is-set A
  is-setⁱ→is-set A-setⁱ x y p q =
    let z = A-setⁱ x y (Id≃path.from p) (Id≃path.from q)
        w = apⁱ Id≃path.to z
    in Id≃path.to (subst² _＝ⁱ_ (Id≃path.ε _) (Id≃path.ε _) w)


is-discreteⁱ→is-discrete : is-discreteⁱ A → is-discrete A
is-discreteⁱ→is-discrete d = Dec.dmap Id≃path.to (contra Id≃path.from) (d _ _)

is-discrete→is-discreteⁱ : is-discrete A → is-discreteⁱ A
is-discrete→is-discreteⁱ d _ _ = Dec.dmap Id≃path.from (contra Id≃path.to) d

-- opacitiy breaks solvers
instance
  id-is-discrete : ∀ {ℓ} {A : Type ℓ} {x y : A} ⦃ d : Dec (x ＝ y) ⦄ → Dec (x ＝ⁱ y)
  id-is-discrete ⦃ d ⦄ = Dec.dmap Id≃path.from (contra Id≃path.to) d
