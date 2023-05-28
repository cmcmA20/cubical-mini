{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Foundations.Base
open import Foundations.Cubes.Base

open import Agda.Builtin.Nat public
  using (zero; suc; _+_)
  renaming (Nat to ℕ)

HLevel : Type₀
HLevel = ℕ

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ : Level
  A A′ : Type ℓ
  h : HLevel

is-of-hlevel : HLevel → Type ℓ → Type ℓ
is-of-hlevel 0 A = is-contr A
is-of-hlevel (suc 0) A = is-prop A
is-of-hlevel (suc (suc h)) A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-of-hlevel (suc h) (x ＝ y)

is-of-hlevel-fun : (h : HLevel) {A : Type ℓ} {B : Type ℓ′} (f : A → B) → Type (ℓ ⊔ ℓ′)
is-of-hlevel-fun h f = Π[ b ꞉ _ ] is-of-hlevel h (fibre f b)

-- TODO reformulate directly without using J?
-- is-of-hlevel-Ω→is-of-hlevel
--   : (h : HLevel)
--   → (Π[ x ꞉ A ] is-of-hlevel (suc h) (x ＝ x))
--   → is-of-hlevel (2 + h) A
-- is-of-hlevel-Ω→is-of-hlevel 0 hΩ x y =
--   J (λ y p → (q : x ＝ y) → p ＝ q) (hΩ x refl)
-- is-of-hlevel-Ω→is-of-hlevel (suc n) hΩ x _ =
--   J (λ y p → (q : x ＝ y) → is-of-hlevel (suc n) (p ＝ q)) (hΩ x refl)


-- Essential properties of `is-prop` and `is-contr`

is-prop→pathP : {B : I → Type ℓ}
                (h : (i : I) → is-prop (B i))
              → (b₀ : B i0) (b₁ : B i1)
              → ＜ b₀ ／ B ＼ b₁ ＞
is-prop→pathP h b₀ b₁ = to-pathP (h _ _ _)

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
extend→is-contr ext = (outS (ext i0 λ ())) , λ x i → outS (ext i λ _ → x)

is-contr→is-set : is-contr A → is-set A
is-contr→is-set C x y p q i j = outS (is-contr→extend C (∂ i ∨ ∂ j) λ where
  (i = i0) → p j
  (i = i1) → q j
  (j = i0) → x
  (j = i1) → y)


contractible-if-inhabited : (A → is-contr A) → is-prop A
contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y

inhabited-prop-is-contr : A → is-prop A → is-contr A
inhabited-prop-is-contr x p = x , p x

is-prop→is-set : is-prop A → is-set A
is-prop→is-set h a b p q j i = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → h a a k
  k (i = i1) → h a b k
  k (j = i0) → h a (p i) k
  k (j = i1) → h a (q i) k
  k (k = i0) → a

is-of-hlevel-suc : (h : HLevel) → is-of-hlevel h A → is-of-hlevel (suc h) A
is-of-hlevel-suc 0         x = is-contr→is-prop x
is-of-hlevel-suc (suc 0) x = is-prop→is-set x
is-of-hlevel-suc (suc (suc h)) p x y = is-of-hlevel-suc (suc h) (p x y)

is-of-hlevel-+ : (h₀ h₁ : HLevel) → is-of-hlevel h₀ A → is-of-hlevel (h₁ + h₀) A
is-of-hlevel-+ h₀ 0     x = x
is-of-hlevel-+ h₀ (suc h₁) x = is-of-hlevel-suc _ (is-of-hlevel-+ h₀ h₁ x)

is-prop→is-hlevel-suc : is-prop A → is-of-hlevel (suc h) A
is-prop→is-hlevel-suc {h = 0    } A-prop = A-prop
is-prop→is-hlevel-suc {h = suc h} A-prop =
  is-of-hlevel-suc (suc h) (is-prop→is-hlevel-suc A-prop)

path-is-of-hlevel : (h : HLevel) → is-of-hlevel h A → {x y : A}
                  → is-of-hlevel h (x ＝ y)
path-is-of-hlevel 0 ahl =
  is-contr→is-prop ahl _ _ , is-prop→is-set (is-contr→is-prop ahl) _ _ _
path-is-of-hlevel (suc h) ahl = is-of-hlevel-suc (suc h) ahl _ _

pathP-is-of-hlevel : {A : I → Type ℓ} (h : HLevel)
                   → is-of-hlevel h (A i1)
                   → {x : A i0} {y : A i1}
                   → is-of-hlevel h (PathP A x y)
pathP-is-of-hlevel {A} h ahl {x} {y} =
  subst (is-of-hlevel h) (sym (pathP＝path A x y)) (path-is-of-hlevel h ahl)

path-is-of-hlevel′ : (h : HLevel) → is-of-hlevel (suc h) A → (x y : A) → is-of-hlevel h (x ＝ y)
path-is-of-hlevel′ 0 ahl x y =
  ahl x y , is-prop→is-set ahl _ _ _
path-is-of-hlevel′ (suc h) p x y = p x y

pathP-is-of-hlevel′ : {A : I → Type ℓ} (h : HLevel)
                    → is-of-hlevel (suc h) (A i1)
                    → (x : A i0) (y : A i1)
                    → is-of-hlevel h (PathP A x y)
pathP-is-of-hlevel′ {A} h ahl x y =
  subst (is-of-hlevel h) (sym (pathP＝path A x y)) (path-is-of-hlevel′ h ahl _ _)


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


is-prop→SquareP
  : ∀ {B : I → I → Type ℓ} → ((i j : I) → is-prop (B i j))
  → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
  → (p : PathP (λ j → B j i0) a c)
  → (q : PathP (λ j → B i0 j) a b)
  → (s : PathP (λ j → B i1 j) c d)
  → (r : PathP (λ j → B j i1) b d)
  → SquareP B q s p r
is-prop→SquareP {B} is-propB {a} p q s r i j =
  hcomp (∂ j ∨ ∂ i) λ where
    k (j = i0) → is-propB i j (base i j) (p i) k
    k (j = i1) → is-propB i j (base i j) (r i) k
    k (i = i0) → is-propB i j (base i j) (q j) k
    k (i = i1) → is-propB i j (base i j) (s j) k
    k (k = i0) → base i j
  where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a
