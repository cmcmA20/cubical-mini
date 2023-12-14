{-# OPTIONS --safe #-}
module Data.Id.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Transport

open import Structures.IdentitySystem

open import Correspondences.Discrete

open import Data.Dec.Base as Dec

open import Data.Id.Base public

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


opaque
  unfolding is-of-hlevel
  is-contrⁱ→is-contr : is-contrⁱ A → is-contr A
  is-contrⁱ→is-contr (centre , _) .fst = centre
  is-contrⁱ→is-contr (_ , paths)  .snd = Id≃path.to ∘ paths

  is-propⁱ→is-prop : is-propⁱ A → is-prop A
  is-propⁱ→is-prop A-propⁱ x y = Id≃path.to (A-propⁱ x y)

  is-setⁱ→is-set : is-setⁱ A → is-set A
  is-setⁱ→is-set A-setⁱ x y p q =
    let z = A-setⁱ x y (Id≃path.from p) (Id≃path.from q)
        w = apⁱ Id≃path.to z
    in Id≃path.to (subst² _＝ⁱ_ (Id≃path.ε _) (Id≃path.ε _) w)


is-discreteⁱ→is-discrete : is-discreteⁱ A → is-discrete A
is-discreteⁱ→is-discrete d .is-discrete-β x y =
  Dec.dmap Id≃path.to
           (_∘ Id≃path.from)
           (d x y)

is-discrete→is-discreteⁱ : is-discrete A → is-discreteⁱ A
is-discrete→is-discreteⁱ d x y =
  Dec.dmap Id≃path.from
           (_∘ Id≃path.to)
           (d .is-discrete-β x y)
