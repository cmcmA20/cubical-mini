{-# OPTIONS --safe #-}
module Structures.IdentitySystem.Base where

open import Foundations.Base
  renaming (J to Jₜ ; J-refl to Jₜ-refl; _∙_ to _∙ₚ_)
open import Foundations.Cubes
open import Foundations.HLevel
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Groupoid
open import Meta.Underlying

open import Functions.Equiv.Fibrewise

record
  is-identity-system {ℓ ℓ′} {A : Type ℓ}
    (R : A → A → Type ℓ′)
    (rfl : ∀ a → R a a)
    : Type (ℓ ⊔ ℓ′)
  where
  no-eta-equality
  field
    to-path : ∀ {a b} → R a b → a ＝ b
    to-path-over
      : ∀ {a b} (p : R a b)
      → ＜ rfl a ／ (λ i → R a (to-path p i)) ＼ p ＞

  ΣR-is-contr : ∀ {a} → is-contr (Σ A (R a))
  ΣR-is-contr = is-contr-η $ (_ , rfl _) , λ x i → to-path (x .snd) i , to-path-over (x .snd) i

open is-identity-system public


private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  R : A → A → Type ℓ′

J
  : {r : ∀ a → R a a} {x : A}
  → is-identity-system R r
  → (P : ∀ b → R x b → Type ℓ″)
  → P x (r x)
  → ∀ {b} s → P b s
J ids P pr s =
  transport (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr

J-refl
  : {r : ∀ a → R a a} {x : A}
  → (ids : is-identity-system R r)
  → (P : ∀ b → R x b → Type ℓ″)
  → (p : P x (r x))
  → J ids P p (r x) ＝ p
J-refl {R} {r} {x} ids P p =
  transport (λ i → P (ids .to-path (r x) i) (ids .to-path-over (r x) i)) p ＝⟨⟩
  subst P′ (λ i → ids .to-path (r x) i , ids .to-path-over (r x) i) p      ＝⟨ ap (λ e → subst P′ e p) lemma ⟩
  subst P′ refl p                                                          ＝⟨ transport-refl p ⟩
  p                                                                        ∎
  where
    P′ : Σ _ (R x) → Type _
    P′ (b , r) = P b r

    lemma : Σ-pathP (ids .to-path (r x)) (ids .to-path-over (r x)) ＝ refl
    lemma = is-set-β (is-contr→is-set (ΣR-is-contr ids)) _ _ _ _

to-path-refl-coh
  : {r : ∀ a → R a a}
  → (ids : is-identity-system R r)
  → ∀ x
  → (Σ-pathP (ids .to-path (r x)) (ids .to-path-over (r x))) ＝ refl
to-path-refl-coh {r} ids x = is-set-β (is-contr→is-set (ΣR-is-contr ids)) _ _
  (Σ-pathP (ids .to-path (r x)) (ids .to-path-over (r x))) refl

to-path-refl
  : {r : ∀ a → R a a} {x : A}
  → (ids : is-identity-system R r)
  → ids .to-path (r x) ＝ refl
to-path-refl {r} {x} ids = ap (ap fst) $ to-path-refl-coh ids x

to-path-over-refl
  : {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {x : A}
  → (ids : is-identity-system R r)
  → SquareP (λ i j → R x (to-path-refl ids i j))
      (ids .to-path-over (r x)) refl refl refl
to-path-over-refl {x} ids = ap (ap snd) $ to-path-refl-coh ids x

equiv-path→identity-system
  : {r : ∀ a → R a a}
  → (eqv : ∀ {a b} → R a b ≃ (a ＝ b))
  → (∀ a → Equiv.from eqv refl ＝ r a)
  → is-identity-system R r
equiv-path→identity-system {R} {r} eqv pres′ = ids where opaque
  unfolding is-of-hlevel
  contract : ∀ {a} → is-contr (Σ _ (R a))
  contract = is-of-hlevel-≃ 0 ((total (λ _ → apply eqv) , fibrewise-is-equiv→total-is-equiv (eqv .snd)))
    (_ , singleton-is-prop)

  pres : ∀ {a} → eqv # (r a) ＝ refl
  pres = Equiv.injective₂ (eqv ⁻¹) (Equiv.η eqv _) (pres′ _)

  ids : is-identity-system R r
  ids .to-path = apply eqv
  ids .to-path-over {a} {b} p i =
    is-prop→pathP
    (λ i → is-contr→is-prop (eqv .snd .equiv-proof λ j → eqv .fst p (i ∧ j)))
    (r a , pres)
    (p , refl)
    i .fst

identity-system-gives-path
  : {r : ∀ a → R a a}
  → is-identity-system R r
  → ∀ {x y} → R x y ≃ (x ＝ y)
identity-system-gives-path {R} {r} ids =
  iso→equiv (ids .to-path , iso from ri li) where
    from : ∀ {a b} → a ＝ b → R a b
    from {a} p = transport (λ i → R a (p i)) (r a)

    ri : ∀ {a b} → (from {a} {b}) is-right-inverse-of (ids .to-path)
    ri = Jₜ (λ y p → ids .to-path (from p) ＝ p)
            ( ap (ids .to-path) (transport-refl _)
            ∙ to-path-refl ids)

    li : ∀ {a b} → (from {a} {b}) is-left-inverse-of (ids .to-path)
    li = J ids (λ y p → from (ids .to-path p) ＝ p)
               ( ap from (to-path-refl ids)
               ∙ transport-refl _ )




module _
  {R S : A → A → Type ℓ′}
  {r : ∀ a → R a a} {s : ∀ a → S a a}
  (ids : is-identity-system R r)
  (eqv : ∀ x y → R x y ≃ S x y)
  (pres : ∀ x → eqv x x .fst (r x) ＝ s x)
  where
  private module e x y = Equiv (eqv x y)
  transfer-identity-system : is-identity-system S s
  transfer-identity-system .to-path sab = ids .to-path (e.from _ _ sab)
  transfer-identity-system .to-path-over {a} {b} p i = hcomp (∂ i) λ where
    j (i = i0) → pres a j
    j (i = i1) → e.ε _ _ p j
    j (j = i0) → e.to _ _ (ids .to-path-over (e.from _ _ p) i)

@0 univalence-identity-system
  : is-identity-system {A = Type ℓ} _≃_ (λ _ → refl!)
univalence-identity-system .to-path = ua
univalence-identity-system .to-path-over p =
  Σ-prop-pathP (λ _ → is-equiv-is-prop) $ fun-ext $ λ a → path→ua-pathP p refl

path-identity-system : is-identity-system (Path A) (λ _ → refl)
path-identity-system .to-path = id
path-identity-system .to-path-over p i j = p (i ∧ j)

opaque
  unfolding is-of-hlevel is-contr-η
  is-identity-system-is-prop
    : {R : A → A → Type ℓ′} {r : ∀ a → R a a}
    → is-prop (is-identity-system R r)
  is-identity-system-is-prop {A} {R} {r} =
    retract→is-of-hlevel 1 from to cancel λ x y i a → is-contr-is-prop (x a) (y a) i
    where
      to : is-identity-system R r → ∀ x → is-contr (Σ A (R x))
      to ids x = ΣR-is-contr ids

      sys : ∀ (l : ∀ x → is-contr (Σ A (R x))) a b (s : R a b) (i j : I)
          → Partial (∂ i ∨ ~ j) (Σ A (R a))
      sys l a b s i j (j = i0) = l a .fst
      sys l a b s i j (i = i0) = l a .snd (a , r a) j
      sys l a b s i j (i = i1) = l a .snd (b , s) j

      from : (∀ x → is-contr (Σ A (R x))) → is-identity-system R r
      from x .to-path      {a} {b} s i = hcomp (∂ i) (sys x a b s i) .fst
      from x .to-path-over {a} {b} s i = hcomp (∂ i) (sys x a b s i) .snd

      square : ∀ (x : is-identity-system R r) a b (s : R a b)
             → Square {A = Σ A (R a)}
               (λ i → x .to-path (r a) i , x .to-path-over (r a) i)
               (λ i → x .to-path s i , x .to-path-over s i)
               refl
               (λ i → x .to-path s i , x .to-path-over s i)
      square x a b s i j = hcomp (∂ i ∨ ∂ j) λ where
        k (k = i0) → x .to-path s j , x .to-path-over s j
        k (i = i0) → x .to-path s j , x .to-path-over s j
        k (i = i1) → x .to-path s j , x .to-path-over s j
        k (j = i0) → to-path-refl-coh {R = R} {r = r} x a (~ k) i
        k (j = i1) → b , s

      sys′ : ∀ (x : is-identity-system R r) a b (s : R a b) i j k
           → Partial (∂ i ∨ ∂ j ∨ ~ k) (Σ A (R a))
      sys′ x a b s i j k (k = i0) = x .to-path (r a) i , x .to-path-over (r a) i
      sys′ x a b s i j k (i = i0) = hfill (∂ j) k (sys (to x) a b s j)
      sys′ x a b s i j k (i = i1) =
          x .to-path (x .to-path-over s (k ∨ j)) (k ∧ j)
        , x .to-path-over (x .to-path-over s (k ∨ j)) (k ∧ j)
      sys′ x a b s i j k (j = i0) =
          x .to-path (r a) (k ∨ i) , x .to-path-over (r a) (k ∨ i)
      sys′ x a b s i j k (j = i1) = square x a b s i k

      cancel : from is-left-inverse-of to
      cancel x i .to-path {a} {b} s j      = hcomp (∂ i ∨ ∂ j) (sys′ x a b s i j) .fst
      cancel x i .to-path-over {a} {b} s j = hcomp (∂ i ∨ ∂ j) (sys′ x a b s i j) .snd

  identity-system→is-of-hlevel
    : (n : HLevel) {R : A → A → Type ℓ′} {r : ∀ x → R x x}
    → is-identity-system R r
    → (∀ x y → is-of-hlevel n (R x y))
    → is-of-hlevel (suc n) A
  identity-system→is-of-hlevel zero ids hl x y = ids .to-path (hl _ _ .fst)
  identity-system→is-of-hlevel (suc n) ids hl x y =
    is-of-hlevel-≃ (suc n) (identity-system-gives-path ids ⁻¹) (hl x y)

instance
  H-Level-identity-system : ∀ {n} {r : ∀ a → R a a} → H-Level (suc n) (is-identity-system R r)
  H-Level-identity-system = hlevel-prop-instance is-identity-system-is-prop


set-identity-system
  : {r : ∀ x → R x x}
  → (∀ x y → is-prop (R x y))
  → (∀ {x y} → R x y → x ＝ y)
  → is-identity-system R r
set-identity-system rprop rpath .to-path = rpath
set-identity-system rprop rpath .to-path-over p =
  is-prop→pathP (λ i → rprop _ _) _ p
