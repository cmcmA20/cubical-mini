{-# OPTIONS --safe #-}
module Algebra.Monoid where

open import Foundations.Base hiding (id)
open import Foundations.Equiv

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP

open import Algebra.Semigroup public

private variable
  ℓ : Level
  A : Type ℓ
  e x y : A
  _✦_ : A → A → A
  n : HLevel

Unital-left : (id : A) (_⋆_ : A → A → A) → Type _
Unital-left {A} id _⋆_ = Π[ x ꞉ A ] (id ⋆ x ＝ x)

Unital-right : (id : A) (_⋆_ : A → A → A) → Type _
Unital-right {A} id _⋆_ = Π[ x ꞉ A ] (x ⋆ id ＝ x)

Raw-∞-monoid-on : Type ℓ → Type ℓ
Raw-∞-monoid-on X = X × (X → X → X)

Wild-∞-monoid-on : Type ℓ → Type ℓ
Wild-∞-monoid-on X = Σ[ id ꞉ X ] Σ[ _⋆_ ꞉ (X → X → X) ]
  (Associative _⋆_ × Unital-left id _⋆_ × Unital-right id _⋆_)


-- 2-monoids

record 2-monoid {A : Type ℓ} (id : A) (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field has-2-semigroup : 2-semigroup _⋆_
  open 2-semigroup has-2-semigroup public

  field
    id-l   : Unital-left id _⋆_
    id-r   : Unital-right id _⋆_
    id-coh :  ap (_⋆ y) (id-r x)
           ＝ sym (assoc x id y)
            ∙ ap (x ⋆_) (id-l y)

unquoteDecl 2-monoid-iso = declare-record-iso 2-monoid-iso (quote 2-monoid)

2-monoid-is-set : is-set (2-monoid e _✦_)
2-monoid-is-set = is-set-η λ x → let open 2-monoid x in is-set-β
  (is-of-hlevel-≃ 2 (iso→equiv 2-monoid-iso) hlevel!) x

instance
  H-Level-2-monoid : H-Level (2 + n) (2-monoid e _✦_)
  H-Level-2-monoid = hlevel-basic-instance 2 2-monoid-is-set


2-Monoid-on : Type ℓ → Type ℓ
2-Monoid-on X = Σ[ id ꞉ X ] Σ[ _⋆_ ꞉ (X → X → X) ] (2-monoid id _⋆_)

2-Monoid : (ℓ : Level) → Type (ℓsuc ℓ)
2-Monoid ℓ = Σ[ X ꞉ Type ℓ ] 2-Monoid-on X


-- monoids

record is-monoid {A : Type ℓ} (id : A) (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field has-is-semigroup : is-semigroup _⋆_
  open is-semigroup has-is-semigroup public

  field
    id-l : Unital-left  id _⋆_
    id-r : Unital-right id _⋆_

unquoteDecl is-monoid-iso = declare-record-iso is-monoid-iso (quote is-monoid)

is-monoid-is-prop : is-prop (is-monoid e _✦_)
is-monoid-is-prop = is-prop-η λ x → let open is-monoid x in is-prop-β
  (is-of-hlevel-≃ 1 (iso→equiv is-monoid-iso) hlevel!) x

instance
  H-Level-is-monoid : H-Level (suc n) (is-monoid e _✦_)
  H-Level-is-monoid = hlevel-prop-instance is-monoid-is-prop

Monoid-on : Type ℓ → Type ℓ
Monoid-on X = Σ[ (id , _⋆_) ꞉ X × (X → X → X) ] (is-monoid id _⋆_)

private
  monoid-desc : Desc ℓ ℓ Raw-∞-monoid-on ℓ
  monoid-desc .Desc.descriptor = auto-str-term!
  monoid-desc .Desc.axioms _ = is-monoid $²_
  monoid-desc .Desc.axioms-prop _ _ = is-monoid-is-prop

monoid-str : Structure ℓ _
monoid-str = desc→structure monoid-desc

@0 monoid-str-is-univalent : is-univalent (monoid-str {ℓ})
monoid-str-is-univalent = desc→is-univalent monoid-desc

Monoid : (ℓ : Level) → Type (ℓsuc ℓ)
Monoid ℓ = Σ[ X ꞉ Type ℓ ] Monoid-on X


-- monoid theory

module _ {A* : Monoid-on A} where
  private
    _⋆_ = A* .fst .snd
    id = A* .fst .fst
    open is-monoid (A* .snd)

  iter-l : ℕ → A → A
  iter-l 0       _ = id
  iter-l (suc n) x = iter-l n x ⋆ x

  iter-r : ℕ → A → A
  iter-r 0       _ = id
  iter-r (suc n) x = x ⋆ iter-r n x

  iter-comm : (n : ℕ) → x ⋆ iter-r n x ＝ iter-r n x ⋆ x
  iter-comm 0       = id-r _ ∙ sym (id-l _)
  iter-comm (suc n) = ap (_ ⋆_) (iter-comm n) ∙ assoc _ _ _

  iter-unique : (n : ℕ) → iter-l n x ＝ iter-r n x
  iter-unique 0       = refl
  iter-unique (suc n) = ap (_⋆ _) (iter-unique n) ∙ sym (iter-comm n)
