{-# OPTIONS --safe #-}
module Meta.Search.HLevel where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel public
open import Foundations.Sigma

open import Meta.Literals.FromProduct
open import Meta.Reflection
open import Meta.Search.Base public

open import Structures.n-Type
open Structures.n-Type public
  using ( n-Type; el; Underlying-n-Type
        ; Prop ; Set )

open import Correspondences.Erased

open import Data.Empty.Base
open import Data.Bool.Base
open import Data.Fin.Base
import Data.List.Base as List
open List public
  using ([] ; _∷_)
open List
open import Data.List.Instances.FromProduct
open import Data.Maybe.Base

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  C : (a : A) (b : B a) → Type ℓc
  D : (a : A) (b : B a) (c : C a b) → Type ℓd
  n : HLevel

instance
  Tactic-hlevel : Tactic-desc (quote is-of-hlevel) by-hlevel
  Tactic-hlevel .Tactic-desc.args-length = 3
  Tactic-hlevel .Tactic-desc.goal-selector = fsuc (fsuc fzero)
  Tactic-hlevel .Tactic-desc.level-selector = fsuc fzero
  Tactic-hlevel .Tactic-desc.aliases
    = (quote is-contr , 0 , 2 , fsuc fzero)
    ∷ (quote is-prop  , 1 , 2 , fsuc fzero)
    ∷ (quote is-set   , 2 , 2 , fsuc fzero)
    ∷ []
  Tactic-hlevel .Tactic-desc.other-atoms = [ quote _≃_ , quote ¬_ ]
  Tactic-hlevel .Tactic-desc.instance-name = quote H-Level
  Tactic-hlevel .Tactic-desc.instance-helper = quote hlevel
  Tactic-hlevel .Tactic-desc.upwards-closure = just (quote is-of-hlevel-+)

hlevel-tactic-worker = search-tactic-worker Tactic-hlevel
macro hlevel! = hlevel-tactic-worker

el! : (A : Type ℓ) {@(tactic hlevel-tactic-worker) hl : is-of-hlevel n A} → n-Type ℓ n
el! A {hl} = el A hl

prop-extₑ!
  : {B : Type ℓb}
    {@(tactic hlevel-tactic-worker) aprop : is-prop A}
    {@(tactic hlevel-tactic-worker) bprop : is-prop B}
  → (A → B) → (B → A)
  → A ≃ B
prop-extₑ! {aprop} {bprop} = prop-extₑ aprop bprop

Σ-prop-path!
  : {@(tactic hlevel-tactic-worker) bxprop : ∀ x → is-prop (B x)}
  → {x y : Σ A B}
  → x .fst ＝ y .fst
  → x ＝ y
Σ-prop-path! {bxprop} = Σ-prop-path bxprop

prop!
  : {A : I → Type ℓ} {@(tactic hlevel-tactic-worker) aip : is-prop (A i0)}
  → {x : A i0} {y : A i1}
  → ＜ x ／ A ＼ y ＞
prop! {A} {aip} {x} {y} =
  is-prop→pathP (λ i → coe0→i (λ j → is-prop (A j)) i aip) x y

instance
  decomp-hlevel-lift : goal-decomposition (quote is-of-hlevel) (Lift ℓ′ A)
  decomp-hlevel-lift = decomp (quote Lift-is-of-hlevel) [ `level-same , `search (quote is-of-hlevel) ]

  decomp-hlevel-fun : {B : Type ℓb} → goal-decomposition (quote is-of-hlevel) (A → B)
  decomp-hlevel-fun = decomp (quote fun-is-of-hlevel) [ `level-same , `search (quote is-of-hlevel) ]

  decomp-hlevel-prod : {B : Type ℓb} → goal-decomposition (quote is-of-hlevel) (A × B)
  decomp-hlevel-prod = decomp (quote ×-is-of-hlevel)
    [ `level-same , `search (quote is-of-hlevel) , `search (quote is-of-hlevel) ]

  decomp-hlevel-pi³ : goal-decomposition (quote is-of-hlevel) (∀ a b c → D a b c)
  decomp-hlevel-pi³ = decomp (quote Π³-is-of-hlevel)
    [ `level-same , `search-under 3 (quote is-of-hlevel) ]

  decomp-hlevel-pi² : goal-decomposition (quote is-of-hlevel) (∀ a b → C a b)
  decomp-hlevel-pi² = decomp (quote Π³-is-of-hlevel) [ `level-same , `search-under 2 (quote is-of-hlevel) ]

  decomp-hlevel-pi : goal-decomposition (quote is-of-hlevel) (∀ a → B a)
  decomp-hlevel-pi = decomp (quote Π-is-of-hlevel) [ `level-same , `search-under 1 (quote is-of-hlevel) ]

  decomp-hlevel-impl-pi : goal-decomposition (quote is-of-hlevel) (∀ {a} → B a)
  decomp-hlevel-impl-pi = decomp (quote Π-is-of-hlevel-implicit) [ `level-same , `search-under 1 (quote is-of-hlevel) ]

  decomp-hlevel-erased-prop : goal-decomposition (quote is-of-hlevel) ∥ A ∥ᴱ
  decomp-hlevel-erased-prop = decomp (quote ∥-∥ᴱ-is-prop)
    [ `search (quote is-of-hlevel) ]

  decomp-hlevel-erased : goal-decomposition (quote is-of-hlevel) ∥ A ∥ᴱ
  decomp-hlevel-erased = decomp (quote ∥-∥ᴱ-is-of-hlevel)
    [ `level-same , `search (quote is-of-hlevel) ]

  decomp-hlevel-equiv-right : {B : Type ℓb} → goal-decomposition (quote is-of-hlevel) (A ≃ B)
  decomp-hlevel-equiv-right = decomp (quote ≃-is-of-hlevel-right-suc) [ `level-minus 1 , `search (quote is-of-hlevel) ]

  decomp-hlevel-equiv-left : {B : Type ℓb} → goal-decomposition (quote is-of-hlevel) (A ≃ B)
  decomp-hlevel-equiv-left = decomp (quote ≃-is-of-hlevel-left-suc) [ `level-minus 1 , `search (quote is-of-hlevel) ]

  decomp-hlevel-equiv : {B : Type ℓb} → goal-decomposition (quote is-of-hlevel) (A ≃ B)
  decomp-hlevel-equiv = decomp (quote ≃-is-of-hlevel) [ `level-same , `search (quote is-of-hlevel) , `search (quote is-of-hlevel) ]

  decomp-hlevel-sigma : goal-decomposition (quote is-of-hlevel) (Σ A B)
  decomp-hlevel-sigma = decomp (quote Σ-is-of-hlevel)
    [ `level-same , `search (quote is-of-hlevel) , `search-under 1 (quote is-of-hlevel) ]

  decomp-hlevel-univalence : {A B : Type ℓ} → goal-decomposition (quote is-of-hlevel) (A ＝ B)
  decomp-hlevel-univalence = decomp (quote ＝-is-of-hlevel)
    [ `level-same , `search (quote is-of-hlevel) , `search (quote is-of-hlevel) ]

  decomp-hlevel-path : {a b : A} → goal-decomposition (quote is-of-hlevel) (a ＝ b)
  decomp-hlevel-path = decomp (quote path-is-of-hlevel)
    [ `level-same , `search (quote is-of-hlevel) ]

  decomp-hlevel-path′ : {a b : A} → goal-decomposition (quote is-of-hlevel) (a ＝ b)
  decomp-hlevel-path′ = decomp (quote path-is-of-hlevel′)
    [ `level-suc , `search (quote is-of-hlevel) , `meta , `meta ]

  decomp-hlevel-pathP′ : {F : I → Type ℓ} {a : F i0} {b : F i1}
                       → goal-decomposition (quote is-of-hlevel) ＜ a ／ F ＼ b ＞
  decomp-hlevel-pathP′ = decomp (quote pathP-is-of-hlevel′)
    [ `level-suc , `search (quote is-of-hlevel) , `meta , `meta ]

  decomp-hlevel-ntype : goal-decomposition (quote is-of-hlevel) (n-Type ℓ n)
  decomp-hlevel-ntype = decomp (quote n-Type-is-of-hlevel) [ `level-minus 1 ]

  decomp-hlevel-hlevel : goal-decomposition (quote is-of-hlevel) (is-of-hlevel n A)
  decomp-hlevel-hlevel = decomp (quote is-of-hlevel-is-of-hlevel-suc) [ `level-minus 1 ]

  decomp-hlevel-is-equiv : {B : Type ℓ′} {f : A → B} → goal-decomposition (quote is-of-hlevel) (is-equiv f)
  decomp-hlevel-is-equiv = decomp (quote is-equiv-is-of-hlevel) []

  proj-hlevel-n-type : Struct-proj-desc (quote is-of-hlevel) by-hlevel (quote n-Type.carrier) true
  proj-hlevel-n-type .Struct-proj-desc.struct-name = quote n-Type
  proj-hlevel-n-type .Struct-proj-desc.struct-args-length = 2
  proj-hlevel-n-type .Struct-proj-desc.goal-projection = quote n-Type.carrier-is-tr
  proj-hlevel-n-type .Struct-proj-desc.projection-args-length = 3
  proj-hlevel-n-type .Struct-proj-desc.level-selector = fsuc fzero
  proj-hlevel-n-type .Struct-proj-desc.carrier-selector = fsuc (fsuc fzero)

-- Usage
private
  module _ {A : Set ℓ} {B : ⌞ A ⌟ → n-Type ℓ 3} where
    some-def = ⌞ A ⌟
    _ : is-set (⌞ A ⌟ → ⌞ A ⌟)
    _ = hlevel!

    _ : is-of-hlevel 2 (⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
    _ = hlevel!

    _ : is-of-hlevel 3 (Σ some-def λ x → ⌞ B x ⌟)
    _ = hlevel!

    _ : ∀ a → is-of-hlevel 5 (⌞ A ⌟ × ⌞ A ⌟ × (ℕ → ⌞ B a ⌟))
    _ = hlevel!

    _ : ∀ a → is-of-hlevel 3 (⌞ A ⌟ × ⌞ A ⌟ × (ℕ → ⌞ B a ⌟))
    _ = hlevel!

    _ : (w z : Term) (x : ℕ) (r : ⌞ A ⌟) → is-of-hlevel 2 ⌞ A ⌟
    _ = hlevel!

    _ : (a : ℕ) (x y : ⌞ A ⌟) → is-prop (x ＝ y)
    _ = hlevel!

    -- this one uses `H-Level-nType` instance which is compile-time only
    @0 _ : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
    _ = hlevel!

    @0 _ : is-of-hlevel 3 ∥ ⌞ A ⌟ ∥ᴱ
    _ = hlevel!

    _ : ∀ n (x : n-Type ℓ n) → is-of-hlevel (2 + n) ⌞ x ⌟
    _ = λ n x → hlevel!
