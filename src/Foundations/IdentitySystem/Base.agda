{-# OPTIONS --safe #-}
module Foundations.IdentitySystem.Base where

open import Foundations.Base
open import Foundations.Cubes
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Sigma
open import Foundations.Univalence

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

  singleton-is-contr : ∀ {a} → is-contr (Σ A (R a))
  singleton-is-contr .fst = _ , rfl _
  singleton-is-contr .snd x i = to-path (x .snd) i , to-path-over (x .snd) i

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

to-path-refl-coh
  : {A : Type ℓ} {R : A → A → Type ℓ′}
    {r : (a : A) → R a a}
  → (ids : is-identity-system R r)
  → ∀ x
  → (ids .to-path (r x) ,ₚ ids .to-path-over (r x)) ＝ refl
to-path-refl-coh {r} ids x = is-contr→is-set (singleton-is-contr ids) _ _
  (ids .to-path (r x) ,ₚ ids .to-path-over (r x)) refl

J-refl
  : {r : ∀ a → R a a} {x : A}
  → (ids : is-identity-system R r)
  → (P : ∀ b → R x b → Type ℓ″)
  → (p : P x (r x))
  → J ids P p (r x) ＝ p
J-refl {R} {r} {x} ids P p =
  transport (λ i → P (ids .to-path (r x) i) (ids .to-path-over (r x) i)) p  ~⟨⟩
  subst (P $²_) (λ i → ids .to-path (r x) i , ids .to-path-over (r x) i) p  ~⟨ ap (λ e → subst (P $²_) e p) (to-path-refl-coh ids x) ⟩
  subst (P $²_) refl p                                                      ~⟨ transport-refl p ⟩
  p                                                                         ∎

to-path-refl
  : {A : Type ℓ} {R : A → A → Type ℓ′}
    {r : (a : A) → R a a} {x : A}
  → (ids : is-identity-system R r)
  → ids .to-path (r x) ＝ refl
to-path-refl {r} {x} ids = ap (ap fst) $ to-path-refl-coh ids x

to-path-over-refl
  : {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {x : A}
  → (ids : is-identity-system R r)
  → Squareᴾ (λ i j → R x (to-path-refl ids i j))
      (ids .to-path-over (r x)) refl refl refl
to-path-over-refl {x} ids = ap (ap snd) $ to-path-refl-coh ids x

singleton-is-contr→identity-system
  : {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  → (∀ {a} → is-contr (Σ _ (R a)))
  → is-identity-system R r
singleton-is-contr→identity-system {R} {r} c = ids where
  paths′ : ∀ {a} (p : Σ _ (R a)) → (a , r a) ＝ p
  paths′ p = is-contr→is-prop c _ _

  ids : is-identity-system R r
  ids .to-path      p = ap fst (paths′ (_ , p))
  ids .to-path-over p = ap snd (paths′ (_ , p))

equiv-path→identity-system
  : {A : Type ℓ} {R : A → A → Type ℓ′}
    {r : (a : A) → R a a}
  → (eqv : ∀ {a b} → R a b ≃ (a ＝ b))
  → is-identity-system R r
equiv-path→identity-system e = singleton-is-contr→identity-system $
  ≃→is-of-hlevel! 0 ((total (λ _ → e .fst)) , fibrewise-is-equiv→total-is-equiv (e .snd))

identity-system-gives-path
  : {r : ∀ a → R a a}
  → is-identity-system R r
  → ∀ {x y} → R x y ≃ (x ＝ y)
identity-system-gives-path {R} {r} ids =
  ≅→≃ (ids .to-path , iso from ri li) where
    from : ∀ {a b} → a ＝ b → R a b
    from {a} p = transport (λ i → R a (p i)) (r a)

    ri : ∀ {a b} → (from {a} {b}) is-right-inverse-of (ids .to-path)
    ri = Jₚ (λ y p → ids .to-path (from p) ＝ p)
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
  : is-identity-system {A = Type ℓ} _≃_ (λ _ → refl)
univalence-identity-system .to-path = ua
univalence-identity-system .to-path-over p =
  Σ-prop-pathᴾ (λ _ → is-equiv-is-prop) $ fun-ext $ λ a → =→ua-pathᴾ p refl

path-identity-system : {A : Type ℓ} → is-identity-system (Path A) (λ _ → refl)
path-identity-system .to-path = id
path-identity-system .to-path-over p i j = p (i ∧ j)

opaque
  is-identity-system-is-prop
    : {R : A → A → Type ℓ′} {r : ∀ a → R a a}
    → is-prop (is-identity-system R r)
  is-identity-system-is-prop {A} {R} {r} =
    retract→is-of-hlevel 1 from to cancel λ x y i a → is-contr-is-prop (x a) (y a) i
    where
      to : is-identity-system R r → ∀ x → is-contr (Σ A (R x))
      to ids x = singleton-is-contr ids

      from : (∀ x → is-contr (Σ A (R x))) → is-identity-system R r
      from x = singleton-is-contr→identity-system (x _)

      cancel′
        : ∀ (x : is-identity-system R r) {a b} (s : R a b)
        → Path ((a , r a) ＝ (b , s))
            (singleton-is-contr (from (to x)) .snd (b , s))
            (singleton-is-contr x .snd (b , s))
      cancel′ x s = is-prop→squareᴾ (λ _ _ → is-contr→is-prop (singleton-is-contr x)) _ _ _ _

      cancel : from is-left-inverse-of to
      cancel x i .to-path s = ap fst (cancel′ x s i)
      cancel x i .to-path-over s = ap snd (cancel′ x s i)

  identity-system→is-of-hlevel
    : (n : HLevel) {R : A → A → Type ℓ′} {r : ∀ x → R x x}
    → is-identity-system R r
    → (∀ x y → is-of-hlevel n (R x y))
    → is-of-hlevel (suc n) A
  identity-system→is-of-hlevel zero ids hl x y = ids .to-path (hl _ _ .fst)
  identity-system→is-of-hlevel (suc n) ids hl x y =
    ≃→is-of-hlevel (suc n) (identity-system-gives-path ids ⁻¹) (hl x y)

instance opaque
  H-Level-identity-system : ∀ {n} {r : ∀ a → R a a} → H-Level (suc n) (is-identity-system R r)
  H-Level-identity-system = hlevel-prop-instance is-identity-system-is-prop


set-identity-system
  : {r : ∀ x → R x x}
  → (∀ x y → is-prop (R x y))
  → (∀ {x y} → R x y → x ＝ y)
  → is-identity-system R r
set-identity-system rprop rpath .to-path = rpath
set-identity-system rprop rpath .to-path-over p =
  is-prop→pathᴾ (λ i → rprop _ _) _ p


-- Automation

set-identity-system!
  : {r : ∀ x → R x x}
  → ⦃ R-pr : ∀ {x y} → H-Level 1 (R x y) ⦄
  → (∀ {x y} → R x y → x ＝ y)
  → is-identity-system R r
set-identity-system! = set-identity-system λ _ _ → hlevel 1

opaque
  identity-system→is-of-hlevel!
    : (n : HLevel) {R : A → A → Type ℓ′} {r : ∀ x → R x x}
    → is-identity-system R r
    → ⦃ ∀ {x y} → H-Level n (R x y) ⦄
    → is-of-hlevel (suc n) A
  identity-system→is-of-hlevel! n ids =
    identity-system→is-of-hlevel n ids λ _ _ → hlevel n
