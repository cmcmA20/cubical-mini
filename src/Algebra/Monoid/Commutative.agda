{-# OPTIONS --safe #-}
module Algebra.Monoid.Commutative where

open import Foundations.Base hiding (id)

open import Meta.Marker
open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP

open import Algebra.Monoid public

private variable
  ℓ : Level
  A : Type ℓ
  e x y z : A
  _✦_ : A → A → A

Commutative : (_⋆_ : A → A → A) → Type _
Commutative {A} _⋆_ = Π[ x ꞉ A ] Π[ y ꞉ A ] (y ⋆ x ＝ x ⋆ y)

Wild-braided∞-monoid-on : Type ℓ → Type ℓ
Wild-braided∞-monoid-on X = Σ[ id ꞉ X ] Σ[ _⋆_ ꞉ (X → X → X) ]
  (Associative _⋆_ × Unital-left id _⋆_ × Unital-right id _⋆_ × Commutative _⋆_)


-- (braided?) 2-monoids

record braided-2-monoid {A : Type ℓ} (id : A) (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field has-2-monoid : 2-monoid id _⋆_
  open 2-monoid has-2-monoid public

  field
    braiding     : Commutative _⋆_
    braiding-coh :  assoc y z x ∙ braiding x (y ⋆ z) ∙ assoc x y z
                 ＝ ap (y ⋆_) (braiding x z) ∙ assoc y x z ∙ ap (_⋆ z) (braiding x y)

unquoteDecl braided-2-monoid-iso = declare-record-iso braided-2-monoid-iso (quote braided-2-monoid)

instance
  braided-2-monoid-is-set : is-set (braided-2-monoid e _✦_)
  braided-2-monoid-is-set = is-set-η λ x → let open braided-2-monoid x in is-set-β
    (is-of-hlevel-≃ 2 (iso→equiv braided-2-monoid-iso) hlevel!) x

braided-2-monoid-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) (braided-2-monoid e _✦_)
braided-2-monoid-is-of-hlevel n = is-of-hlevel-+-left 2 n braided-2-monoid-is-set

instance
  decomp-hlevel-braided-2-monoid : goal-decomposition (quote is-of-hlevel) (braided-2-monoid e _✦_)
  decomp-hlevel-braided-2-monoid = decomp (quote braided-2-monoid-is-of-hlevel) (`level-minus 2 ∷ [])

Braided-2-monoid-on : Type ℓ → Type ℓ
Braided-2-monoid-on X = Σ[ id ꞉ X ] Σ[ _⋆_ ꞉ (X → X → X) ] (braided-2-monoid id _⋆_)

Braided-2-monoid : (ℓ : Level) → Type (ℓsuc ℓ)
Braided-2-monoid ℓ = Σ[ X ꞉ Type ℓ ] Braided-2-monoid-on X


-- symmetric 2-monoids

record sym-2-monoid {A : Type ℓ} (id : A) (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field has-braided-2-monoid : braided-2-monoid id _⋆_
  open braided-2-monoid has-braided-2-monoid public

  field braiding-sym : braiding x y ∙ braiding y x ＝ refl

unquoteDecl sym-2-monoid-iso = declare-record-iso sym-2-monoid-iso (quote sym-2-monoid)

instance
  sym-2-monoid-is-set : is-set (sym-2-monoid e _✦_)
  sym-2-monoid-is-set = is-set-η λ x → let open sym-2-monoid x in is-set-β
    (is-of-hlevel-≃ 2 (iso→equiv sym-2-monoid-iso) hlevel!) x

sym-2-monoid-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) (sym-2-monoid e _✦_)
sym-2-monoid-is-of-hlevel n = is-of-hlevel-+-left 2 n sym-2-monoid-is-set

instance
  decomp-hlevel-sym-2-monoid : goal-decomposition (quote is-of-hlevel) (sym-2-monoid e _✦_)
  decomp-hlevel-sym-2-monoid = decomp (quote sym-2-monoid-is-of-hlevel) (`level-minus 2 ∷ [])

Sym-2-monoid-on : Type ℓ → Type ℓ
Sym-2-monoid-on X = Σ[ id ꞉ X ] Σ[ _⋆_ ꞉ (X → X → X) ] (sym-2-monoid id _⋆_)

Sym-2-monoid : (ℓ : Level) → Type (ℓsuc ℓ)
Sym-2-monoid ℓ = Σ[ X ꞉ Type ℓ ] Sym-2-monoid-on X


-- commutative monoids

record is-comm-monoid {A : Type ℓ} (id : A) (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field has-is-monoid : is-monoid id _⋆_
  open is-monoid has-is-monoid public

  field comm : Commutative _⋆_

unquoteDecl is-comm-monoid-iso = declare-record-iso is-comm-monoid-iso (quote is-comm-monoid)

instance
  is-comm-monoid-is-prop : is-prop (is-comm-monoid e _✦_)
  is-comm-monoid-is-prop = is-prop-η λ x → let open is-comm-monoid x in is-prop-β
    (is-of-hlevel-≃ 1 (iso→equiv is-comm-monoid-iso) hlevel!) x

Comm-monoid-on : Type ℓ → Type ℓ
Comm-monoid-on X = Σ[ (id , _⋆_) ꞉ X × (X → X → X) ] (is-comm-monoid id _⋆_)

private
  comm-monoid-desc : Desc ℓ ℓ Raw-∞-monoid-on ℓ
  comm-monoid-desc .Desc.descriptor = auto-str-term!
  comm-monoid-desc .Desc.axioms _ = is-comm-monoid $²_
  comm-monoid-desc .Desc.axioms-prop _ _ = is-comm-monoid-is-prop

comm-monoid-str : Structure ℓ _
comm-monoid-str = desc→structure comm-monoid-desc

@0 comm-monoid-str-is-univalent : is-univalent (comm-monoid-str {ℓ = ℓ})
comm-monoid-str-is-univalent = desc→is-univalent comm-monoid-desc

Comm-monoid : (ℓ : Level) → Type (ℓsuc ℓ)
Comm-monoid ℓ = Σ[ X ꞉ Type ℓ ] Comm-monoid-on X


-- abelian monoid theory

module _ {A* : Comm-monoid-on A} where
  private
    _⋆_ = A* .fst .snd
    id = A* .fst .fst
    open is-comm-monoid (A* .snd)

  exchange : (x ⋆ y) ⋆ z ＝ (x ⋆ z) ⋆ y
  exchange {x} {y} {z} =
    (x ⋆ y) ⋆ z     ＝˘⟨ assoc _ _ _ ⟩
    x ⋆ ⌜ y  ⋆ z ⌝  ＝⟨ ap! (comm _ _) ⟩
    x ⋆ (z  ⋆ y)    ＝⟨ assoc _ _ _ ⟩
    (x ⋆ z) ⋆ y     ∎
