
module Algebra.Semigroup where

open import Foundations.Base
open import Foundations.Path
open import Meta.Search.HLevel
open import Meta.Record

open import Algebra.Magma

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A

record is-semigroup {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  field
    has-is-magma : is-magma _⋆_
    associative  : (x y z : A) → x ⋆ (y ⋆ z) ＝ (x ⋆ y) ⋆ z
    associative-coh :
      {a b c d : A}
          → (associative a b (c ⋆ d) ∙ associative (a ⋆ b) c d)
         ＝ ap (a ⋆_) (associative _ _ _)
         ∙ associative a (b ⋆ c) d
         ∙ ap (_⋆ d) (associative _ _ _)

  open is-magma has-is-magma public

open is-semigroup public

private
  eqv :
    {_⋆_ : A → A → A}
         → Iso (is-semigroup _⋆_)
           (is-magma _⋆_
         × (Σ[ associative ꞉ ((x y z : A) → x ⋆ (y ⋆ z) ＝ (x ⋆ y) ⋆ z) ]
            ({a b c d : A}
            → (associative a b (c ⋆ d) ∙ associative (a ⋆ b) c d)
            ＝ ap (a ⋆_) (associative b c d)
            ∙ associative a (b ⋆ c) d
            ∙ ap (_⋆ d) (associative a b c))))
  unquoteDef eqv = define-record-iso eqv (quote is-semigroup)

record Semigroup-on (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    _⋆_ : A → A → A

    has-is-semigroup : is-semigroup _⋆_

Semigroup : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
Semigroup ℓ = Σ[ A ꞉ 𝒰 ℓ ] Semigroup-on A

is-semigroup-is-set : {_⋆_ : A → A → A} → is-set (is-semigroup _⋆_)
is-semigroup-is-set {_⋆_} = is-set-η λ x y →
  let open is-semigroup x in
  is-set-β
    (is-of-hlevel-≃ 2 (iso→equiv eqv)
      (Σ-is-of-hlevel 2
        (is-prop→is-set hlevel!)
        λ magma → Σ-is-of-hlevel 2
          (Π³-is-of-hlevel 2
          (λ a a₁ a₂ →
              path-is-of-hlevel′ 2 (hlevel 3)
                (a ⋆ (a₁ ⋆ a₂)) ((a ⋆ a₁) ⋆ a₂)))
          (λ a →
            Π-is-of-hlevel-implicit 2
            (λ a₁ →
                Π-is-of-hlevel-implicit 2
                (λ a₂ →
                  Π-is-of-hlevel-implicit 2
                  (λ a₃ → Π-is-of-hlevel-implicit 2 (λ a₄ →
                    path-is-of-hlevel′
                      2
                      hlevel!
                      _
                      _)
                  )
                )
            )
          )
      )
    )
    x y
