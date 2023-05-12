{-# OPTIONS --safe #-}
module Foundations.HLevel where

open import Prim.Data.Nat

open import Foundations.Base

HLevel : Type₀
HLevel = ℕ
pattern 0𝒽 = zero
pattern 𝒽suc h = suc h

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ : Level
  A A′ : Type ℓ

is-of-hlevel : HLevel → Type ℓ → Type ℓ
is-of-hlevel 0𝒽 A = is-contr A
is-of-hlevel (𝒽suc 0𝒽) A = is-prop A
is-of-hlevel (𝒽suc (𝒽suc h)) A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-of-hlevel (𝒽suc h) (x ＝ y)

record is-of-HLevel (h : HLevel) {ℓ} (A : Type ℓ) : Type ℓ where
  eta-equality
  field iohl : is-of-hlevel h A
open is-of-HLevel ⦃ ... ⦄ public

is-Contr : Type ℓ → Type ℓ
is-Contr = is-of-HLevel 0𝒽

is-Prop : Type ℓ → Type ℓ
is-Prop = is-of-HLevel (𝒽suc 0𝒽)

is-Set : Type ℓ → Type ℓ
is-Set = is-of-HLevel (𝒽suc (𝒽suc 0𝒽))

is-Groupoid : Type ℓ → Type ℓ
is-Groupoid = is-of-HLevel (𝒽suc (𝒽suc (𝒽suc 0𝒽)))

is-of-hlevel-fun : (h : HLevel) {A : Type ℓ} {B : Type ℓ′} (f : A → B) → Type (ℓ ⊔ ℓ′)
is-of-hlevel-fun h f = Π[ b ꞉ _ ] is-of-hlevel h (fibre f b)


-- TODO reformulate directly without using J
is-of-hlevel-Ω→is-of-hlevel
  : (h : HLevel)
  → (Π[ x ꞉ A ] is-of-hlevel (𝒽suc h) (x ＝ x))
  → is-of-hlevel (2 + h) A
is-of-hlevel-Ω→is-of-hlevel 0𝒽 hΩ x y =
  J (λ y p → (q : x ＝ y) → p ＝ q) (hΩ x refl)
is-of-hlevel-Ω→is-of-hlevel (𝒽suc n) hΩ x _ =
  J (λ y p → (q : x ＝ y) → is-of-hlevel (𝒽suc n) (p ＝ q)) (hΩ x refl)


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

is-contr-is-prop : is-prop (is-contr A)
is-contr-is-prop (c₀ , h₀) (c₁ , h₁) j .fst = h₀ c₁ j
is-contr-is-prop (c₀ , h₀) (c₁ , h₁) j .snd y i = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → h₀ (h₀ c₁ j) k
  k (i = i1) → h₀ y k
  k (j = i0) → h₀ (h₀ y i) k
  k (j = i1) → h₀ (h₁ y i) k
  k (k = i0) → c₀

is-prop→is-set : is-prop A → is-set A
is-prop→is-set h a b p q j i = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → h a a k
  k (i = i1) → h a b k
  k (j = i0) → h a (p i) k
  k (j = i1) → h a (q i) k
  k (k = i0) → a

is-prop-is-prop : is-prop (is-prop A)
is-prop-is-prop f g i a b = is-prop→is-set f a b (f a b) (g a b) i

contractible-if-inhabited : (A → is-contr A) → is-prop A
contractible-if-inhabited cont x y = is-contr→is-prop (cont x) x y

inhabited-prop-is-contr : A → is-prop A → is-contr A
inhabited-prop-is-contr x p = x , p x
