{-# OPTIONS --safe #-}
module Foundations.HLevel.Base where

open import Prim.Data.Nat

open import Foundations.Base

HLevel : Type₀
HLevel = ℕ
pattern 0𝒽 = zero
pattern 𝒽suc h = suc h

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ : Level
  A A′ : Type ℓ
  h : HLevel

is-of-hlevel : HLevel → Type ℓ → Type ℓ
is-of-hlevel 0𝒽 A = is-contr A
is-of-hlevel (𝒽suc 0𝒽) A = is-prop A
is-of-hlevel (𝒽suc (𝒽suc h)) A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-of-hlevel (𝒽suc h) (x ＝ y)

-- record is-of-HLevel (h : HLevel) {ℓ} (A : Type ℓ) : Type ℓ where
--   eta-equality
--   field iohl : is-of-hlevel h A
-- open is-of-HLevel ⦃ ... ⦄ public

-- is-Contr : Type ℓ → Type ℓ
-- is-Contr = is-of-HLevel 0𝒽

-- is-Prop : Type ℓ → Type ℓ
-- is-Prop = is-of-HLevel (𝒽suc 0𝒽)

-- is-Set : Type ℓ → Type ℓ
-- is-Set = is-of-HLevel (𝒽suc (𝒽suc 0𝒽))

-- is-Groupoid : Type ℓ → Type ℓ
-- is-Groupoid = is-of-HLevel (𝒽suc (𝒽suc (𝒽suc 0𝒽)))

is-of-hlevel-fun : (h : HLevel) {A : Type ℓ} {B : Type ℓ′} (f : A → B) → Type (ℓ ⊔ ℓ′)
is-of-hlevel-fun h f = Π[ b ꞉ _ ] is-of-hlevel h (fibre f b)


-- TODO reformulate directly without using J?
-- is-of-hlevel-Ω→is-of-hlevel
--   : (h : HLevel)
--   → (Π[ x ꞉ A ] is-of-hlevel (𝒽suc h) (x ＝ x))
--   → is-of-hlevel (2 + h) A
-- is-of-hlevel-Ω→is-of-hlevel 0𝒽 hΩ x y =
--   J (λ y p → (q : x ＝ y) → p ＝ q) (hΩ x refl)
-- is-of-hlevel-Ω→is-of-hlevel (𝒽suc n) hΩ x _ =
--   J (λ y p → (q : x ＝ y) → is-of-hlevel (𝒽suc n) (p ＝ q)) (hΩ x refl)


-- Essential properties of `is-prop` and `is-contr`

is-prop→PathP : {B : I → Type ℓ}
                (h : (i : I) → is-prop (B i))
              → (b₀ : B i0) (b₁ : B i1)
              → ＜ b₀ ／ B ＼ b₁ ＞
is-prop→PathP h b₀ b₁ = to-PathP (h _ _ _)

-- Amy says it's more efficient to use direct cubical proof
is-contr→is-prop : is-contr A → is-prop A
is-contr→is-prop (centre , paths) x y i = hcomp (∂ i) λ where
  j (i = i0) → paths x j
  j (i = i1) → paths y j
  j (j = i0) → centre

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

is-of-hlevel-suc : (h : HLevel) → is-of-hlevel h A → is-of-hlevel (𝒽suc h) A
is-of-hlevel-suc 0𝒽         x = is-contr→is-prop x
is-of-hlevel-suc (𝒽suc 0𝒽) x = is-prop→is-set x
is-of-hlevel-suc (𝒽suc (𝒽suc h)) p x y = is-of-hlevel-suc (𝒽suc h) (p x y)

is-of-hlevel-+ : (h₀ h₁ : HLevel) → is-of-hlevel h₀ A → is-of-hlevel (h₁ + h₀) A
is-of-hlevel-+ h₀ 0𝒽     x = x
is-of-hlevel-+ h₀ (suc h₁) x = is-of-hlevel-suc _ (is-of-hlevel-+ h₀ h₁ x)

is-prop→is-hlevel-suc : is-prop A → is-of-hlevel (𝒽suc h) A
is-prop→is-hlevel-suc {h = 0𝒽    } A-prop = A-prop
is-prop→is-hlevel-suc {h = 𝒽suc h} A-prop =
  is-of-hlevel-suc (𝒽suc h) (is-prop→is-hlevel-suc A-prop)

Path-is-of-hlevel : (h : HLevel) → is-of-hlevel h A → {x y : A}
                  → is-of-hlevel h (x ＝ y)
Path-is-of-hlevel 0𝒽 ahl =
  is-contr→is-prop ahl _ _ , is-prop→is-set (is-contr→is-prop ahl) _ _ _
Path-is-of-hlevel (𝒽suc h) ahl = is-of-hlevel-suc (𝒽suc h) ahl _ _

PathP-is-of-hlevel : {A : I → Type ℓ} (h : HLevel)
                   → is-of-hlevel h (A i1)
                   → {x : A i0} {y : A i1}
                   → is-of-hlevel h (PathP A x y)
PathP-is-of-hlevel {A} h ahl {x} {y} =
  subst (is-of-hlevel h) (sym (PathP＝Path A x y)) (Path-is-of-hlevel h ahl)

Path-is-of-hlevel′ : (h : HLevel) → is-of-hlevel (𝒽suc h) A → (x y : A) → is-of-hlevel h (x ＝ y)
Path-is-of-hlevel′ 0𝒽 ahl x y =
  ahl x y , is-prop→is-set ahl _ _ _
Path-is-of-hlevel′ (𝒽suc h) p x y = p x y

PathP-is-of-hlevel′ : {A : I → Type ℓ} (h : HLevel)
                    → is-of-hlevel (𝒽suc h) (A i1)
                    → (x : A i0) (y : A i1)
                    → is-of-hlevel h (PathP A x y)
PathP-is-of-hlevel′ {A} h ahl x y =
  subst (is-of-hlevel h) (sym (PathP＝Path A x y)) (Path-is-of-hlevel′ h ahl _ _)


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
is-of-hlevel-is-prop 0𝒽 = is-contr-is-prop
is-of-hlevel-is-prop (𝒽suc 0𝒽) = is-prop-is-prop
is-of-hlevel-is-prop (𝒽suc (𝒽suc h)) x y i a b =
  is-of-hlevel-is-prop (𝒽suc h) (x a b) (y a b) i
