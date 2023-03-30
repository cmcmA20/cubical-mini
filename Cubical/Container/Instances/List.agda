{-# OPTIONS --safe #-}
module Cubical.Container.Instances.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat.Base
open import Cubical.Data.List renaming (List to ListI)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base as ⊎
open import Cubical.Data.FinSum.Base

open import Cubical.Container.Base

ListC : Container _ _
ListC = ℕ ▶ Fin

private variable
  ℓ : Level
  A : Type ℓ

List : Type ℓ → Type ℓ
List = ⟦ ListC ⟧

private module _ where
  to : ListI A → List A
  to []       = 0 , λ ()
  to (x ∷ xs) with to xs
  ... | n , lookup = suc n , ⊎.rec (λ _ → x) lookup

  from : (n : ℕ) (lookup : Fin n → A) → ListI A
  from zero    _      = []
  from (suc n) lookup = lookup fzero ∷ from n (lookup ∘ fsuc)

  toFrom : (n : ℕ) (lookup : Fin n → A) → to (uncurry from (n , lookup)) ≡ (n , lookup)
  toFrom zero    _      = ΣPathP (refl , funExt λ ())
  toFrom (suc n) lookup = let ih = toFrom n (lookup ∘ fsuc)
    in ΣPathP $ cong (suc ∘ fst) ih
              , toPathP (funExt λ { (inl  _) → transportRefl _
                                  ; (fsuc k) → cong (_$ k) $ fromPathP $ cong snd ih
                                  } )

  fromTo : (xs : ListI A) → uncurry from (to xs) ≡ xs
  fromTo []       = refl
  fromTo (x ∷ xs) = cong (x ∷_) (fromTo xs)

ListContainerIso : Iso (ListI A) (List A)
Iso.fun      ListContainerIso = to
Iso.inv      ListContainerIso = uncurry from
Iso.rightInv ListContainerIso = uncurry toFrom
Iso.leftInv  ListContainerIso = fromTo

ListContainerEquiv : ListI A ≃ List A
ListContainerEquiv = isoToEquiv ListContainerIso

@0 ListContainer≡ : ListI {ℓ} ≡ List
ListContainer≡ = funExt λ _ → ua ListContainerEquiv
