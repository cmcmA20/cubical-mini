{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive where

open import Foundations.Prelude
  renaming ( _$_  to _$ₜ_
           ; _$²_ to _$ₜ²_

           ; refl to reflₚ
           ; sym  to symₚ
           ; _∙_  to _∙ₚ_
           )

open import Meta.Variadic

open import Correspondences.Binary.Reflexive
open import Correspondences.Binary.Symmetric
open import Correspondences.Binary.Transitive

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Sum.Base as ⊎
open import Data.Sum.Path as ⊎

open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Properties

private variable
  m n k : ℕ

infix 3 _≤_ _<_ _≥_ _>_
        _≰_ _≮_ _≱_ _≯_

data _≤_ : ℕ → ℕ → Type where
  instance
    z≤ : 0 ≤ n
  s≤s : m ≤ n → suc m ≤ suc n

_<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_ : ℕ → ℕ → Type

m < n = suc m ≤ n
m ≥ n = n ≤ m
m > n = n < m
m ≰ n = ¬ m ≤ n
m ≮ n = ¬ m < n
m ≱ n = ¬ m ≥ n
m ≯ n = ¬ m > n


-- Properties of order

instance
  s≤s′ : ⦃ p : m ≤ n ⦄ → suc m ≤ suc n
  s≤s′ ⦃ p ⦄ = s≤s p

  ≤-refl : n ≤ n
  ≤-refl {(zero)} = z≤
  ≤-refl {suc n}  = s≤s ≤-refl
{-# INCOHERENT ≤-refl #-}

≤-trans : m ≤ n → n ≤ k → m ≤ k
≤-trans z≤      z≤      = z≤
≤-trans z≤      (s≤s q) = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-antisym : m ≤ n → n ≤ m → m ＝ n
≤-antisym z≤      z≤      = refl
≤-antisym (s≤s p) (s≤s q) = ap suc (≤-antisym p q)

opaque
  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop z≤      z≤      = refl
  ≤-is-prop (s≤s p) (s≤s q) = ap s≤s (≤-is-prop p q)

instance opaque
  H-Level-≤ : H-Level (suc k) (m ≤ n)
  H-Level-≤ = hlevel-prop-instance ≤-is-prop

≤-peel : suc m ≤ suc n → m ≤ n
≤-peel (s≤s p) = p

≤-peel-unpeel : (p : suc m ≤ suc n) → s≤s (≤-peel p) ＝ p
≤-peel-unpeel (s≤s _) = refl

≤-suc-r : m ≤ n → m ≤ suc n
≤-suc-r z≤      = z≤
≤-suc-r (s≤s p) = s≤s (≤-suc-r p)

instance
 ≤-suc-r′ : ⦃ m≤n : m ≤ n ⦄ → m ≤ suc n
 ≤-suc-r′ ⦃ m≤n ⦄ = ≤-suc-r m≤n
{-# INCOHERENT ≤-suc-r′ #-}

≤-ascend : n ≤ suc n
≤-ascend = ≤-suc-r ≤-refl

suc≰id : suc n ≰ n
suc≰id (s≤s p) = suc≰id p

s≰z : suc n ≰ 0
s≰z = λ ()

≤-subst : {a b c d : ℕ} → a ＝ b → c ＝ d → a ≤ c → b ≤ d
≤-subst a=b c=d = transport $ ap² (_≤_) a=b c=d


-- Properties of strict order

<-irr : n ≮ n
<-irr (s≤s p) = <-irr p

s<s : m < n → suc m < suc n
s<s = s≤s

<-peel : suc m < suc n → m < n
<-peel = ≤-peel

<-weaken : (x y : ℕ) → x < y → x ≤ y
<-weaken x (suc y) (s≤s p) = ≤-suc-r p

<-trans : {x y z : ℕ} → x < y → y < z → x < z
<-trans x<y y<z = ≤-trans x<y (<-weaken _ _ y<z)

<-weaken-z : (x y : ℕ) → x < y → 0 < y
<-weaken-z x (suc y) (s≤s _) = s≤s z≤

<-asym : ∀[ _<_ →̇ _≯_ ]
<-asym (s≤s p) (s≤s q) = <-asym p q

<-suc-r : m < n → m < suc n
<-suc-r = ≤-suc-r

<-suc-l : suc m < n → m < n
<-suc-l p = <-trans ≤-refl p

<-ascend : n < suc n
<-ascend = ≤-refl

≮z : n ≮ 0
≮z = s≰z

z<s : 0 < suc n
z<s = s≤s z≤


-- Decidability

≤-dec : (m n : ℕ) → Dec (m ≤ n)
≤-dec zero zero = yes z≤
≤-dec zero (suc y) = yes z≤
≤-dec (suc x) zero = no λ ()
≤-dec (suc x) (suc y) with ≤-dec x y
... | yes x≤y = yes (s≤s x≤y)
... | no ¬x≤y = no (λ { (s≤s x≤y) → ¬x≤y x≤y })

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with ≤-dec (suc m) n
≤-split m n | yes m<n = inl m<n
≤-split m n | no m≥n with ≤-dec (suc n) m
≤-split m n | no m≥n | yes n<m = inr (inl n<m)
≤-split m n | no m≥n | no n≥m  = inr (inr (go m n m≥n n≥m)) where
  go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
  go zero zero p q          = refl
  go zero (suc zero) p q    = absurd $ p $ s≤s z≤
  go zero (suc (suc n)) p q = absurd $ p $ s≤s z≤
  go (suc zero) zero p q    = absurd $ q $ s≤s z≤
  go (suc (suc m)) zero p q = absurd $ q $ s≤s z≤
  go (suc m) (suc n) p q    = ap suc $ go m n (p ∘ s≤s) (q ∘ s≤s)


-- Addition

≤-+-l : (x y : ℕ) → x ≤ y + x
≤-+-l zero    y = z≤
≤-+-l (suc x) y = transport (sym (ap (suc x ≤_) (+-suc-r y x))) (s≤s (≤-+-l x y))

≤-weak-+l : (x y z : ℕ) → x ≤ z → x ≤ y + z
≤-weak-+l x  zero   z p = p
≤-weak-+l x (suc y) z p = ≤-suc-r (≤-weak-+l x y z p)

≤-cong-+ : (m n p q : ℕ) → m ≤ p → n ≤ q → m + n ≤ p + q
≤-cong-+ zero    n  p      q u v = ≤-weak-+l n p q v
≤-cong-+ (suc m) n (suc p) q u v = s≤s (≤-cong-+ m n p q (≤-peel u) v)


-- Subtraction

suc-pred : (n : ℕ) → 0 < n → n ＝ suc (pred n)
suc-pred (suc n) n0 = refl

+-sub : (p q : ℕ) → q ≤ p → p ∸ q + q ＝ p
+-sub  p       zero   qp = +-zero-r p
+-sub (suc p) (suc q) qp = +-suc-r _ _ ∙ ap suc (+-sub p q (≤-peel qp))

≤-sub-lr : (p q r : ℕ) → p ≤ q + r → p ∸ r ≤ q
≤-sub-lr  p      q  zero   pqr = subst (λ x → p ≤ x) (+-zero-r q) pqr
≤-sub-lr  zero   q (suc r) pqr = z≤
≤-sub-lr (suc p) q (suc r) pqr = ≤-sub-lr p q r (≤-peel (subst (λ x → suc p ≤ x) (+-suc-r q r) pqr))

<-sub-lr : (p q r : ℕ) → 0 < q → p < q + r → p ∸ r < q
<-sub-lr p (suc q) r _ pqr = s≤s (≤-sub-lr p q r (≤-peel pqr))


-- Multiplication

≤-·l : (a b c : ℕ) → b ≤ c → a · b ≤ a · c
≤-·l  zero   b c p = z≤
≤-·l (suc a) b c p = ≤-cong-+ b (a · b) c (a · c) p (≤-·l a b c p)

·-inj-r : (x y z : ℕ) → 0 < z → x · z ＝ y · z → x ＝ y
·-inj-r zero y .(suc z) (s≤s {n = z} _) H with (·-zero y (suc z) (sym H))
... | inl prf = sym prf
... | inr prf = absurd (suc≠zero prf)
·-inj-r (suc x) zero .(suc z) (s≤s {n = z} prf) H = absurd (suc≠zero H)
·-inj-r (suc x) (suc y) .(suc z) (s≤s {n = z} prf) H =
  ap suc $ ·-inj-r x y (suc z) (s≤s prf) (+-inj-l z (x · suc z) (y · suc z) (suc-inj H))

·-inj-l : (x y z : ℕ) → 0 < x → x · y ＝ x · z → y ＝ z
·-inj-l x y z 0<x p = ·-inj-r _ _ _ 0<x (·-comm y x ∙ p ∙ ·-comm x z)

z<· : (m n : ℕ) → (0 < m · n) → (0 < m) × (0 < n)
z<· (suc m) zero    0<mn = absurd (s≰z (subst (0 <_) (·-absorb-r m) 0<mn))
z<· (suc _) (suc _) _    = s≤s z≤ , s≤s z≤


-- Conversion

=→≤ : ∀[ _＝_ {A = ℕ} →̇ _≤_ ]
=→≤ p = ≤-subst refl p ≤-refl

<→≤ : ∀[ _<_ →̇ _≤_ ]
<→≤ p = ≤-trans ≤-ascend p

<→≠ : ∀[ _<_ →̇ _≠_ {A = ℕ} ]
<→≠ {x = m} {x = n} m<n m=n = suc≰id (subst (_≤ n) (ap suc m=n) m<n)

≤≃≯ : (m ≤ n) ≃ (m ≯ n)
≤≃≯ = prop-extₑ! ≤→≯ ≯→≤ where
  ≤→≯ : ∀[ _≤_ →̇ _≯_ ]
  ≤→≯ (s≤s p) (s≤s q) = ≤→≯ p q

  ≯→≤ : ∀[ _≯_ →̇ _≤_ ]
  ≯→≤ {x = m} {x = n} f =
    [ (λ p → absurd $ f $ <→≤ p)
    , [ ≤-peel
      , (λ p → absurd $ f $ =→≤ p)
      ]ᵤ
    ]ᵤ $ ≤-split (suc n) m

≤≃<⊎= : (m ≤ n)
      ≃ (m < n) ⊎ (m ＝ n)
≤≃<⊎= = prop-extₑ (hlevel 1) (disjoint-⊎-is-prop! (<→≠ $ₜ²_)) ≤→<⊎= <⊎=→≤
  where
  ≤→<⊎= : ∀[ _≤_ →̇ _<_ ⊎̇ _＝_ {A = ℕ} ]
  ≤→<⊎= {x = 0}     {x = 0}     z≤      = inr refl
  ≤→<⊎= {x = 0}     {x = suc n} z≤      = inl (s≤s z≤)
  ≤→<⊎= {x = suc m} {x = suc n} (s≤s p) = ⊎.dmap s≤s (ap suc) $ ≤→<⊎= p

  <⊎=→≤ : ∀[ _<_ ⊎̇ _＝_ {A = ℕ} →̇ _≤_ ]
  <⊎=→≤ {x = m} {x = n} = [ <→≤ , =→≤ ]ᵤ

<≃≱ : (m < n) ≃ (m ≱ n)
<≃≱ = prop-extₑ! <→≱ ≱→< where
  <→≱ : ∀[ _<_ →̇ _≱_ ]
  <→≱ m<n m≥n = (≤≃≯ # m≥n)  m<n

  ≱→< : ∀[ _≱_ →̇ _<_ ]
  ≱→< p = ≤≃≯ ⁻¹ $ (p ∘ ≤-peel)

≤≃≤+l : (n ≤ k) ≃ (m + n ≤ m + k)
≤≃≤+l {n} {k} {m} = prop-extₑ! (ff m n k) (gg m n k)
  where
  ff : (a b c : ℕ) → b ≤ c → a + b ≤ a + c
  ff zero    b c p = p
  ff (suc a) b c p = s≤s (ff a b c p)

  gg : (a b c : ℕ) → a + b ≤ a + c → b ≤ c
  gg  zero   b c p = p
  gg (suc a) b c p = gg a b c (≤-peel p)

≤≃≤+r : (m ≤ n) ≃ (m + k ≤ n + k)
≤≃≤+r {m} {n} {k} = ≤≃≤+l ∙ prop-extₑ!
  (≤-subst (+-comm k m) (+-comm k n))
  (≤-subst (+-comm m k) (+-comm n k))

<≃<+l : (n < k) ≃ (m + n < m + k)
<≃<+l {n} {k} {m} = ≤≃≤+l ∙ prop-extₑ!
  (≤-subst (+-suc-r m n) refl)
  (≤-subst (+-suc-r m n ⁻¹) refl)

<≃<+r : (m < n) ≃ (m + k < n + k)
<≃<+r = ≤≃≤+r
