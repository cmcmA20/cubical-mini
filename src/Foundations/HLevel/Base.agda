{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Foundations.Base
open import Foundations.Cubes

open import Agda.Builtin.Nat public
  using (zero; suc; _+_)
  renaming (Nat to ℕ)

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ : Level
  A A′ : Type ℓ
  B : A → Type ℓ′
  h h₁ h₂ : HLevel

is-groupoid : Type ℓ → Type ℓ
is-groupoid = is-of-hlevel 3

is-2-groupoid : Type ℓ → Type ℓ
is-2-groupoid = is-of-hlevel 4

opaque
  is-of-hlevel-Ω→is-of-hlevel
    : (h : HLevel)
    → Π[ x ꞉ A ] is-of-hlevel (1 + h) (x ＝ x)
    → is-of-hlevel (2 + h) A
  is-of-hlevel-Ω→is-of-hlevel 0 hΩ x _ =
    J (λ y p → Π[ q ꞉ x ＝ y ] (p ＝ q)) $ hΩ x refl
  is-of-hlevel-Ω→is-of-hlevel (suc h) hΩ x _ =
    J (λ y p → Π[ q ꞉ x ＝ y ] is-of-hlevel (suc h) (p ＝ q)) $ hΩ x refl


  -- Essential properties of `is-prop` and `is-contr`

  is-prop→pathᴾ : {B : I → Type ℓ}
                  (h : (i : I) → is-prop (B i))
                → (b₀ : B i0) (b₁ : B i1)
                → ＜ b₀ ／ B ＼ b₁ ＞
  is-prop→pathᴾ h b₀ b₁ = to-pathᴾ (h _ _ _)

  -- Amy says it's more efficient to use direct cubical proof
  is-contr→is-prop : is-contr A → is-prop A
  is-contr→is-prop (centre , paths) x y i = hcomp (∂ i) λ where
    j (i = i0) → paths x j
    j (i = i1) → paths y j
    j (j = i0) → centre

  is-contr→extend : is-contr A → (φ : I) (p : Partial φ A) → A [ φ ↦ p ]
  is-contr→extend C φ p = inS (hcomp φ
    λ { j (φ = i1) → C .snd (p 1=1) j
      ; j (j = i0) → C .fst
      })

  extend→is-contr : (∀ φ (p : Partial φ A) → A [ φ ↦ p ]) → is-contr A
  extend→is-contr ext = outS (ext i0 λ ()) , λ x i → outS (ext i λ _ → x)


  contractible-if-inhabited : (A → is-contr A) → is-prop A
  contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y

inhabited-prop-is-contr : A → is-prop A → is-contr A
inhabited-prop-is-contr x p = x , p x

opaque
  is-prop→is-set : is-prop A → is-set A
  is-prop→is-set h a b p q j i = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → h a a k
    k (i = i1) → h a b k
    k (j = i0) → h a (p i) k
    k (j = i1) → h a (q i) k
    k (k = i0) → a

  is-of-hlevel-suc : (h : HLevel) → is-of-hlevel h A → is-of-hlevel (suc h) A
  is-of-hlevel-suc 0       x = is-contr→is-prop x
  is-of-hlevel-suc (suc 0) x = is-prop→is-set x
  is-of-hlevel-suc (suc (suc h)) p x y = is-of-hlevel-suc (suc h) (p x y)

is-of-hlevel-+ : (h₀ h₁ : HLevel) → is-of-hlevel h₀ A → is-of-hlevel (h₁ + h₀) A
is-of-hlevel-+ h₀ 0     x = x
is-of-hlevel-+ h₀ (suc h₁) x = is-of-hlevel-suc (h₁ + h₀) (is-of-hlevel-+ h₀ h₁ x)

is-of-hlevel-+-left : (h₀ h₁ : HLevel) → is-of-hlevel h₀ A → is-of-hlevel (h₀ + h₁) A
is-of-hlevel-+-left {A} h₀ h₁ A-hl =
  subst (λ h → is-of-hlevel h A) (+-comm h₀ h₁) (is-of-hlevel-+ h₀ h₁ A-hl) where
    +-comm : ∀ n k → k + n ＝ n + k
    +-comm 0 k = go k where
      go : ∀ k → k + 0 ＝ k
      go zero = refl
      go (suc x) = ap suc (go x)
    +-comm (suc n) k = go n k ∙ ap suc (+-comm n k) where
      go : ∀ n k → k + suc n ＝ suc (k + n)
      go n zero = refl
      go n (suc k) = ap suc (go n k)

opaque
  is-contr→is-set : is-contr A → is-set A
  is-contr→is-set = is-of-hlevel-+-left 0 2

  is-prop→is-of-hlevel-suc : is-prop A → is-of-hlevel (suc h) A
  is-prop→is-of-hlevel-suc {h = 0    } A-prop = A-prop
  is-prop→is-of-hlevel-suc {h = suc h} A-prop =
    is-of-hlevel-suc (suc h) (is-prop→is-of-hlevel-suc {h = h} A-prop)

  path-is-of-hlevel-same : (h : HLevel) → is-of-hlevel h A → {x y : A}
                         → is-of-hlevel h (x ＝ y)
  path-is-of-hlevel-same 0 ahl =
    is-contr→is-prop ahl _ _ , is-prop→is-set (is-contr→is-prop ahl) _ _ _
  path-is-of-hlevel-same (suc h) ahl = is-of-hlevel-suc (suc h) ahl _ _

  pathᴾ-is-of-hlevel-same : {A : I → Type ℓ} (h : HLevel)
                          → is-of-hlevel h (A i1)
                          → {x : A i0} {y : A i1}
                          → is-of-hlevel h ＜ x ／ A ＼ y ＞
  pathᴾ-is-of-hlevel-same {A} h ahl {x} {y} =
    subst (is-of-hlevel h) (sym (pathᴾ＝path A x y)) (path-is-of-hlevel-same h ahl)

path-is-of-hlevel : (h : HLevel) → is-of-hlevel (suc h) A → (x y : A) → is-of-hlevel h (x ＝ y)
path-is-of-hlevel 0 ahl x y =
  ahl x y , is-prop→is-set ahl _ _ _
path-is-of-hlevel (suc h) p x y = p x y

pathᴾ-is-of-hlevel : {A : I → Type ℓ} (h : HLevel)
                   → is-of-hlevel (suc h) (A i1)
                   → (x : A i0) (y : A i1)
                   → is-of-hlevel h ＜ x ／ A ＼ y ＞
pathᴾ-is-of-hlevel {A} h ahl x y =
  subst (is-of-hlevel h) (sym (pathᴾ＝path A x y)) (path-is-of-hlevel h ahl _ _)


opaque
  is-contr-is-prop : is-prop (is-contr A)
  is-contr-is-prop (c₀ , h₀) (c₁ , h₁) j .fst = h₀ c₁ j
  is-contr-is-prop (c₀ , h₀) (c₁ , h₁) j .snd y i = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → h₀ (h₀ c₁ j) k
    k (i = i1) → h₀ y k
    k (j = i0) → h₀ (h₀ y i) k
    k (j = i1) → h₀ (h₁ y i) k
    k (k = i0) → c₀

  is-prop-is-prop : is-prop (is-prop A)
  is-prop-is-prop f g i a b = is-prop→is-set f a b (f a b) (g a b) i

  is-of-hlevel-is-prop : (h : HLevel) → is-prop (is-of-hlevel h A)
  is-of-hlevel-is-prop 0 = is-contr-is-prop
  is-of-hlevel-is-prop (suc 0) = is-prop-is-prop
  is-of-hlevel-is-prop (suc (suc h)) x y i a b =
    is-of-hlevel-is-prop (suc h) (x a b) (y a b) i

  is-of-hlevel-is-of-hlevel-suc : (h₁ : HLevel) → is-of-hlevel (suc h₁) (is-of-hlevel h A)
  is-of-hlevel-is-of-hlevel-suc {h} h₁ = is-of-hlevel-+-left 1 h₁ (is-of-hlevel-is-prop h)


-- note that it's shifted up by one
is-of-hlevel-dep : HLevel → (A → Type ℓ′) → Type (level-of-type A ⊔ ℓ′)
is-of-hlevel-dep 0 B =
  ∀ {x y} (α : B x) (β : B y) (p : x ＝ y) → ＜ α ／ (λ i → B (p i)) ＼ β ＞
is-of-hlevel-dep (suc n) B =
  ∀ {a₀ a₁} (b₀ : B a₀) (b₁ : B a₁)
  → is-of-hlevel-dep {A = a₀ ＝ a₁} n (λ p → ＜ b₀ ／ (λ i → B (p i)) ＼ b₁ ＞)

opaque
  is-of-hlevel→is-of-hlevel-dep
    : (n : HLevel) → Π[ x ꞉ A ] is-of-hlevel (suc n) (B x)
    → is-of-hlevel-dep n B
  is-of-hlevel→is-of-hlevel-dep 0 hl α β p = is-prop→pathᴾ (λ i → hl (p i)) α β
  is-of-hlevel→is-of-hlevel-dep {A} {B} (suc n) hl {a₀} {a₁} b₀ b₁ =
    is-of-hlevel→is-of-hlevel-dep n (λ p → helper a₁ p b₁)
    where
      helper : (a₁ : A) (p : a₀ ＝ a₁) (b₁ : B a₁)
             → is-of-hlevel (suc n) ＜ b₀ ／ (λ i → B (p i)) ＼ b₁ ＞
      helper a₁ p b₁ =
        J (λ a₁ p → ∀ b₁ → is-of-hlevel (suc n) ＜ b₀ ／ (λ i → B (p i)) ＼ b₁ ＞)
          (λ _ → hl _ _ _) p b₁


  is-prop→squareᴾ
    : {B : I → I → Type ℓ} → ((i j : I) → is-prop (B i j))
    → {a : B i0 i0} {c : B i0 i1} {b : B i1 i0} {d : B i1 i1}
    → (p : ＜ a ／ (λ j → B i0 j) ＼ c ＞)
    → (q : ＜ a ／ (λ i → B i i0) ＼ b ＞)
    → (r : ＜ b ／ (λ j → B i1 j) ＼ d ＞)
    → (s : ＜ c ／ (λ i → B i i1) ＼ d ＞)
    → Squareᴾ B p q r s
  is-prop→squareᴾ {B} B-pr {a} p q r s i j =
    hcomp (∂ j ∨ ∂ i) λ where
      k (j = i0) → B-pr i j (base i j) (q i) k
      k (j = i1) → B-pr i j (base i j) (s i) k
      k (i = i0) → B-pr i j (base i j) (p j) k
      k (i = i1) → B-pr i j (base i j) (r j) k
      k (k = i0) → base i j
    where
      base : (i j : I) → B i j
      base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

is-prop→pathᴾ-is-contr
  : {A : I → Type ℓ} → ((i : I) → is-prop (A i))
  → (x : A i0) (y : A i1) → is-contr ＜ x ／ A ＼ y ＞
is-prop→pathᴾ-is-contr A-pr x y .fst = is-prop→pathᴾ A-pr x y
is-prop→pathᴾ-is-contr A-pr x y .snd p =
  is-prop→squareᴾ (λ _ → A-pr) _ refl p refl

opaque
  is-set→squareᴾ
    : {A : I → I → Type ℓ}
      (is-set : (i j : I) → is-set (A i j))
      {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
      (p : ＜ a ／ (λ j → A j i0) ＼ c ＞)
      (q : ＜ a ／ (λ j → A i0 j) ＼ b ＞)
      (s : ＜ c ／ (λ j → A i1 j) ＼ d ＞)
      (r : ＜ b ／ (λ j → A j i1) ＼ d ＞)
    → Squareᴾ A q p s r
  is-set→squareᴾ is-set a₀₋ a₁₋ a₋₀ a₋₁ =
    transport (sym (pathᴾ＝path _ _ _))
              (pathᴾ-is-of-hlevel 1 (is-set _ _) _ _ _ _)

  -- litmus
  _ : {a b c d : A} (p : a ＝ c) (q : a ＝ b) (r : b ＝ d) (s : c ＝ d)
    → Square p q r s ＝ Squareᴾ (λ _ _ → A) q p s r -- observe the π/2 rotation
  _ = λ _ _ _ _ → refl

  is-set→cast-pathᴾ
    : {x y : A} {p q : x ＝ y} (P : A → Type ℓ′) {px : P x} {py : P y}
    → is-set A
    → ＜ px ／ (λ i → P (p i)) ＼ py ＞
    → ＜ px ／ (λ i → P (q i)) ＼ py ＞
  is-set→cast-pathᴾ {p} {q} P {px} {py} A-set =
    coe0→1 (λ j → ＜ px ／ (λ i → P (A-set _ _ p q j i)) ＼ py ＞)


erased-is-contr : {@0 A : Type ℓ} → @0 is-contr A → is-contr (Erased A)
erased-is-contr (centre , paths) = erase centre , λ where
  (erase x) → congᴱ $ erase (paths x)

opaque
  erased-is-prop : {@0 A : Type ℓ} → @0 is-prop A → is-prop (Erased A)
  erased-is-prop pr (erase x) (erase y) = congᴱ $ erase (pr x y)


-- Automation

record H-Level (n : ℕ) (T : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor hlevel-instance
  field has-of-hlevel : is-of-hlevel n T
{-# INLINE hlevel-instance #-}

open H-Level

hlevel : {ℓ : Level} {A : Type ℓ} (n : HLevel) ⦃ x : H-Level n A ⦄ → is-of-hlevel n A
hlevel n ⦃ x ⦄ = x .has-of-hlevel

prop!
  : {A : I → Type ℓ} ⦃ A-pr : H-Level 1 (A i0) ⦄
  → {x : A i0} {y : A i1}
  → ＜ x ／ A ＼ y ＞
prop! {A} {x} {y} = is-prop→pathᴾ (λ i → coe0→i (λ j → is-prop (A j)) i (hlevel 1)) x y

opaque
  H-Level-is-prop : is-prop (H-Level h A)
  H-Level-is-prop {h} x y i .has-of-hlevel =
    is-of-hlevel-is-prop h (x .has-of-hlevel) (y .has-of-hlevel) i

hlevel-basic-instance : ∀ n → is-of-hlevel n A → ∀ {k} → H-Level (n + k) A
hlevel-basic-instance n hl .has-of-hlevel = is-of-hlevel-+-left n _ hl

opaque
  hlevel-prop-instance : is-prop A → H-Level (suc h) A
  hlevel-prop-instance {h} A-pr .has-of-hlevel = is-prop→is-of-hlevel-suc {h = h} A-pr

-- TODO remove? seems useless if `is-of-hlevel` is transparent
instance opaque
  H-Level-contr : H-Level (suc h) (is-contr A)
  H-Level-contr {h} = hlevel-prop-instance is-contr-is-prop
  {-# INCOHERENT H-Level-contr #-}

  H-Level-prop : H-Level (suc h) (is-prop A)
  H-Level-prop {h} = hlevel-prop-instance is-prop-is-prop
  {-# INCOHERENT H-Level-prop #-}

  H-Level-set : H-Level (suc h) (is-set A)
  H-Level-set {h} = hlevel-prop-instance (is-of-hlevel-is-prop 2)
  {-# INCOHERENT H-Level-set #-}

  H-Level-of-hlevel : H-Level (suc h) (is-of-hlevel h₁ A)
  H-Level-of-hlevel {h₁} = hlevel-prop-instance (is-of-hlevel-is-prop h₁)
  {-# INCOHERENT H-Level-of-hlevel #-}

  H-Level-H-Level : H-Level (suc h) (H-Level h₁ A)
  H-Level-H-Level {h₁} = hlevel-prop-instance H-Level-is-prop

instance
  H-Level-singleton : {a : A} → H-Level h (Singleton a)
  H-Level-singleton {h} = hlevel-basic-instance 0 (singleton-is-contr (_ , refl))
  {-# OVERLAPPING H-Level-singleton #-}
