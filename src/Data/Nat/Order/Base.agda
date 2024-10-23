{-# OPTIONS --safe #-}
module Data.Nat.Order.Base where

open import Meta.Prelude
open Variadics _

open import Logic.Decidability

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects
open import Data.Empty.Properties
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Path
open import Data.Wellfounded.Base

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Order.Inductive.Base
  using ( _≤?_ ; _<?_ ; _≥?_ ; _>?_
        ; _≰?_ ; _≮?_ ; _≱?_ ; _≯?_
        )
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Nat.Solver

private variable
  m n k : ℕ

infix 3 _≤_ _<_ _≥_ _>_
        _≰_ _≮_ _≱_ _≯_

opaque
  _≤_ _<_ : Corr _ (ℕ , ℕ) 0ℓ

  m ≤ n = Σ[ k ꞉ ℕ ] (m + k ＝ n)
  m < n = suc m ≤ n

_≥_ _>_ _≰_ _≮_ _≱_ _≯_ : Corr _ (ℕ , ℕ) 0ℓ

m ≥ n =   n ≤ m
m > n =   n < m
m ≰ n = ¬ m ≤ n
m ≮ n = ¬ m < n
m ≱ n = ¬ m ≥ n
m ≯ n = ¬ m > n


opaque
  unfolding _≤_

  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop (_ , p) (_ , q) = Σ-prop-path! (+-inj-l _ _ _ (p ∙ q ⁻¹))

  <-is-prop : is-prop (m < n)
  <-is-prop = ≤-is-prop

instance opaque
  H-Level-≤ : ⦃ k ≥ʰ 1 ⦄ → H-Level k (m ≤ n)
  H-Level-≤ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance ≤-is-prop
  {-# INCOHERENT H-Level-≤ #-}

  H-Level-< : ⦃ k ≥ʰ 1 ⦄ → H-Level k (m < n)
  H-Level-< ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance <-is-prop
  {-# INCOHERENT H-Level-< #-}

-- Properties of order

opaque
  unfolding _≤_

  z≤ : 0 ≤ n
  z≤ = _ , refl

  s≤s : m ≤ n → suc m ≤ suc n
  s≤s = second (ap suc)

  ≤-peel : suc m ≤ suc n → m ≤ n
  ≤-peel = second suc-inj

  ≤-peel-unpeel : (p : suc m ≤ suc n) → s≤s (≤-peel p) ＝ p
  ≤-peel-unpeel (_ , _) = refl ,ₚ prop!

  ≤-refl : n ≤ n
  ≤-refl = 0 , nat!

  ≤-trans : m ≤ n → n ≤ k → m ≤ k
  ≤-trans {k} (δ₁ , p) (δ₂ , q)
    = δ₁ + δ₂
    , nat! ∙ subst (λ φ → φ + δ₂ ＝ k) (symₚ p) q

  ≤-antisym : m ≤ n → n ≤ m → m ＝ n
  ≤-antisym (0      , p) (_      , _) = sym (+-zero-r _) ∙ p
  ≤-antisym (suc _  , _) (0      , q) = sym q ∙ +-zero-r _
  ≤-antisym {m} (suc δ₁ , p) (suc δ₂ , q) =
    false! $ (+-assoc m _ _ ∙ subst (λ φ → φ + suc δ₂ ＝ m) (sym p) q) ⁻¹

  ≤-suc-r : m ≤ n → m ≤ suc n
  ≤-suc-r = bimap suc λ p → nat! ∙ ap suc p

  ≤-ascend : n ≤ suc n
  ≤-ascend = 1 , nat!

  instance
    Reflects-suc≰id : Reflects (suc n ≤ n) false
    Reflects-suc≰id = ofⁿ λ where (k , p) → false! ((+-suc-r _ k ∙ p) ⁻¹)
    {-# INCOHERENT Reflects-suc≰id #-}

    Reflects-suc≰z : Reflects (suc n ≤ 0) false
    Reflects-suc≰z = ofⁿ (false! ∘ snd)
    {-# INCOHERENT Reflects-suc≰z #-}

  suc≰id : suc n ≰ n
  suc≰id = false!

  s≰z : suc n ≰ 0
  s≰z = false!

  ≤0→=0 : n ≤ 0 → n ＝ 0
  ≤0→=0 {n} (k , p) = +=0-2 n k p .fst

  ≤-subst : {a b c d : ℕ} → a ＝ b → c ＝ d → a ≤ c → b ≤ d
  ≤-subst a=b c=d = second $ subst² (λ u v → u + _ ＝ v) a=b c=d

=→≤ : m ＝ n → m ≤ n
=→≤ {m} {n} e = subst (m ≤_) e ≤-refl

≤≃≤+l : (n ≤ k) ≃ (m + n ≤ m + k)
≤≃≤+l {n} {k} {m} = prop-extₑ! (ff m n k) (gg m n k)
  where
  ff : (a b c : ℕ) → b ≤ c → a + b ≤ a + c
  ff zero    b c p = p
  ff (suc a) b c p = s≤s (ff a b c p)

  gg : (a b c : ℕ) → a + b ≤ a + c → b ≤ c
  gg  zero   b c p = p
  gg (suc a) b c p = gg a b c (≤-peel p)

≤≃≤+r : (n ≤ k) ≃ (n + m ≤ k + m)
≤≃≤+r {n} {k} {m} = ≤≃≤+l ∙ subst (λ q → q ≤ m + k ≃ n + m ≤ k + m) (+-comm n m)
                             (subst (λ q → n + m ≤ q ≃ n + m ≤ k + m) (+-comm k m) refl)

-- Properties of strict order

opaque
  unfolding _<_

  <-irr : n ≮ n
  <-irr = false!

  s<s : m < n → suc m < suc n
  s<s = s≤s

  <-peel : suc m < suc n → m < n
  <-peel = ≤-peel

  <-weaken : (x y : ℕ) → x < y → x ≤ y
  <-weaken x y (δ , p) = suc δ , nat! ∙ p

  <-trans : m < n → n < k → m < k
  <-trans (δ₁ , p) (δ₂ , q)
    = suc (δ₁ + δ₂)
    , nat! ∙ subst (λ φ → suc (φ + δ₂) ＝ _) (symₚ p) q

  <-asym : ∀[ _<_ ⇒ _≯_ ]
  <-asym {x = m} {x = n} (δ₁ , p) (δ₂ , q) = false! u where
    u : m ＝ m + (2 + δ₁ + δ₂)
    u = subst (λ φ → suc (φ + δ₂) ＝ m) (p ⁻¹) q ⁻¹ ∙ nat!

  <-suc-r : m < n → m < suc n
  <-suc-r = ≤-suc-r

  <-suc-l : suc m < n → m < n
  <-suc-l (δ , p) = suc δ , nat! ∙ p

  <-ascend : n < suc n
  <-ascend = 0 , +-zero-r _

  ≮z : n ≮ 0
  ≮z = false!

  z<s : 0 < suc n
  z<s = _ , refl

opaque
  unfolding _≤_ _<_
  <≃<+l : (n < k) ≃ (m + n < m + k)
  <≃<+l {n} {k} {m} = ≤≃≤+l {n = suc n}
                    ∙ subst (λ q → q ≤ m + k ≃ m + n < m + k) (+-suc-r m n ⁻¹) refl

  <≃<+r : (n < k) ≃ (n + m < k + m)
  <≃<+r {n} = ≤≃≤+r {n = suc n}

  ≤-<-trans : {x y z : ℕ} → x ≤ y → y < z → x < z
  ≤-<-trans p = ≤-trans (s≤s p)

  <-≤-trans : {x y z : ℕ} → x < y → y ≤ z → x < z
  <-≤-trans = ≤-trans

-- Conversion

opaque
  unfolding _<_
  <→≤ : ∀[ _<_ ⇒ _≤_ ]
  <→≤ = bimap suc (nat! ∙_)

  <→≠ : ∀[ _<_ ⇒ _≠_ ]
  <→≠ m<n m=n = false! $ subst (_ <_) (sym m=n) m<n

  ≤→≯ : ∀[ _≤_ ⇒ _≯_ ]
  ≤→≯ {x = m} {x = n} (δ₁ , p) (δ₂ , q) = false! u where
    u : m ＝ m + suc (δ₁ + δ₂)
    u = subst (λ φ → suc (φ + δ₂) ＝ m) (symₚ p) q ⁻¹ ∙ nat!

  ≤→<⊎= : ∀[ _≤_ ⇒ _<_ ⊎ _＝_ ]
  ≤→<⊎= (0     , p) = inr $ nat! ∙ p
  ≤→<⊎= (suc δ , p) = inl $ δ , nat! ∙ p

  <⊎=→≤ : ∀[ _<_ ⊎ _＝_ ⇒ _≤_ ]
  <⊎=→≤ (inl m<n) = <→≤ m<n
  <⊎=→≤ (inr m=n) = subst (_≤ _) (sym m=n) ≤-refl

<→≱ : ∀[ _<_ ⇒ _≱_ ]
<→≱ m<n m≥n = ≤→≯ m≥n m<n

≯→≤ : ∀[ _≯_ ⇒ _≤_ ]
≯→≤ {0}     {_}     _ = z≤
≯→≤ {suc _} {0}     f = false! $ f z<s
≯→≤ {suc _} {suc _} f = s≤s $ ≯→≤ (f ∘ s<s)

≱→< : ∀[ _≱_ ⇒ _<_ ]
≱→< {_}     {0}     f = false! $ f z≤
≱→< {0}     {suc _} _ = z<s
≱→< {suc m} {suc n} f = s<s $ ≱→< (f ∘ s≤s)

opaque
  unfolding _<_
  <≃suc≤ : (suc m ≤ n) ≃ (m < n)
  <≃suc≤ = refl

  ≤≃<suc : (m ≤ n) ≃ (m < suc n)
  ≤≃<suc = Σ-ap-snd λ x → s＝s≃

≤≃≯ : (m ≤ n) ≃ (m ≯ n)
≤≃≯ = prop-extₑ! ≤→≯ ≯→≤

<≃≱ : (m < n) ≃ (m ≱ n)
<≃≱ = prop-extₑ! <→≱ ≱→<

≤≃<⊎= : (m ≤ n) ≃ ((m < n) ⊎ (m ＝ n))
≤≃<⊎= = prop-extₑ (hlevel 1) (disjoint-⊎-is-prop! (<→≠ $ₜ²_)) ≤→<⊎= <⊎=→≤


-- Decidability

instance
  <-reflects : Reflects (m < n) (m <? n)
  <-reflects {_}     {0}     = ofⁿ ≮z
  <-reflects {0}     {suc _} = ofʸ z<s
  <-reflects {suc m} {suc n} =
    Reflects.dmap s<s (_∘ <-peel) $ <-reflects {m} {n}

  ≤-reflects : Reflects (m ≤ n) (m ≤? n)
  ≤-reflects {0}     {_}     = ofʸ z≤
  ≤-reflects {suc _} {0}     = ofⁿ false!
  ≤-reflects {suc m} {suc n} =
    Reflects.dmap s≤s (_∘ ≤-peel) $ ≤-reflects {m} {n}

  <-dec : Decidable _<_
  <-dec = _ because auto

  ≤-dec : Decidable _≤_
  ≤-dec = _ because auto

-- TODO use trichotomy
≤-split : Π[ _<_ ⊎ _>_ ⊎ _＝_ ]
≤-split m n = caseᵈ m < n of λ where
  (yes m<n) → inl m<n
  (no  m≮n) → caseᵈ n < m of λ where
    (yes n<m) → inr $ inl n<m
    (no  n≮m) → inr $ inr $ ≤-antisym (≤≃≯ ⁻¹ $ n≮m) (≤≃≯ ⁻¹ $ m≮n)


-- well-foundedness

opaque
  unfolding _<_
  <-ind : ∀ {ℓ″} {P : ℕ → 𝒰 ℓ″}
        → (∀ x → (∀ y → y < x → P y) → P x)
        → ∀ x → P x
  <-ind {P} ih x = go x (suc x) <-ascend
    where
    go : ∀ m n → m < n → P m
    go m  zero   m<n     = false! m<n
    go m (suc n) (q , e) = ih m λ y y<m → go y n (≤-trans y<m (q , suc-inj e))

<-wf : Wf _<_
<-wf = from-induction _<_ λ P → <-ind

-- addition

opaque
  unfolding _≤_
  ≤-+-r : m ≤ m + n
  ≤-+-r {m} {n} = n , refl

≤-+-l : m ≤ n + m
≤-+-l {m} {n} = subst (m ≤_) (+-comm m n) ≤-+-r

<-+-l : m < n → m < k + n
<-+-l m<n = <-≤-trans m<n ≤-+-l

<-+-r : m < n → m < n + k
<-+-r m<n = <-≤-trans m<n ≤-+-r

opaque
  unfolding _<_
  <-+-lr : m < suc n + m
  <-+-lr {m} {n} = n , ap suc (+-comm m n)

<-+-0lr : 0 < n → m < n + m
<-+-0lr {n = zero}  0<n = false! 0<n
<-+-0lr {n = suc n} 0<n = <-+-lr

≤-+ : ∀ {m n p q} → m ≤ p → n ≤ q → m + n ≤ p + q
≤-+ m≤p n≤q = ≤-trans (≤≃≤+r $ m≤p) (≤≃≤+l $ n≤q)

0<≃⊎₁ : ∀ {m n} → 0 < m + n ≃ (0 < m) ⊎₁ (0 < n)
0<≃⊎₁ {m} {n} = prop-extₑ! (∣_∣₁ ∘ 0<→⊎ m n) (elim! [ <-+-r , <-+-l ]ᵤ)
  where
  0<→⊎ : ∀ x y → 0 < x + y → (0 < x) ⊎ (0 < y)
  0<→⊎  zero   y h = inr h
  0<→⊎ (suc x) y _ = inl z<s


-- subtraction

+∸=id : ∀ m n → m ≤ n → m + (n ∸ m) ＝ n
+∸=id  zero    n      m≤n = refl
+∸=id (suc m)  zero   m≤n = false! m≤n
+∸=id (suc m) (suc n) m≤n = ap suc (+∸=id m n (≤-peel m≤n))

∸+=id : ∀ m n → m ≤ n → (n ∸ m) + m ＝ n
∸+=id m n m≤n = +-comm (n ∸ m) m ∙ +∸=id m n m≤n

+∸-assoc : ∀ m n p → p ≤ n → m + (n ∸ p) ＝ m + n ∸ p
+∸-assoc m n p p≤n =
    sym (+-cancel-∸-r (m + (n ∸ p)) p)
  ∙ ap (_∸ p) (sym (+-assoc m (n ∸ p) p))
  ∙ ap (λ q → m + q ∸ p) (+-comm (n ∸ p) p ∙ +∸=id p n p≤n)

∸+-comm : ∀ m n p → n ≤ m → m ∸ n + p ＝ m + p ∸ n
∸+-comm m n p n≤m = +-comm (m ∸ n) p
                  ∙ +∸-assoc p m n n≤m
                  ∙ ap (_∸ n) (+-comm p m)

∸∸-assoc-swap : ∀ m n p → p ≤ n → m ∸ (n ∸ p) ＝ m + p ∸ n
∸∸-assoc-swap m n p p≤n = sym (∸-cancel-+-r m p (n ∸ p)) ∙ ap ((m + p) ∸_) (∸+=id p n p≤n)

∸∸-assoc : ∀ m n p → p ≤ n → n ≤ m → m ∸ (n ∸ p) ＝ m ∸ n + p
∸∸-assoc m n p p≤n n≤m = ∸∸-assoc-swap m n p p≤n ∙ sym (∸+-comm m n p n≤m)

suc-∸ : ∀ m n → m ≤ n → suc (n ∸ m) ＝ (suc n) ∸ m
suc-∸ m n = +∸-assoc 1 n m

∸=0→≤ : m ∸ n ＝ 0 → m ≤ n
∸=0→≤ {m = zero}              _ = z≤
∸=0→≤ {m = suc m} {n = zero}  e = false! e
∸=0→≤ {m = suc m} {n = suc n} e = s≤s (∸=0→≤ {m} {n} e)

opaque
  unfolding _≤_
  ≤→∸=0 : m ≤ n → m ∸ n ＝ 0
  ≤→∸=0 {m} (k , e) = ap (m ∸_) (sym e) ∙ ∸-+-assoc m m k ∙ ap (_∸ k) (∸-cancel m) ∙ ∸-zero-l k

∸=0≃≤ : (m ∸ n ＝ 0) ≃ (m ≤ n)
∸=0≃≤ = prop-extₑ! ∸=0→≤ ≤→∸=0

∸≤≃≤+ : ∀ {m n p} → (m ∸ n ≤ p) ≃ (m ≤ n + p)
∸≤≃≤+ {m} {n} {p} = ∸=0≃≤ ⁻¹ ∙ whisker-path-lₑ (sym (∸-+-assoc n m p)) ∙ ∸=0≃≤

≤-∸-l-≃ : ∀ {m n p} → (m ∸ n ≤ p) ≃ (m ∸ p ≤ n)
≤-∸-l-≃ {m} {n} {p} = ∸≤≃≤+ ∙ subst (λ q → m ≤ n + p ≃ m ≤ q) (+-comm n p) refl ∙ ∸≤≃≤+ ⁻¹

<-∸-r-≃ : ∀ {m n p} → (n < p ∸ m) ≃ (m + n < p)
<-∸-r-≃ {m} {n} {p} = <≃≱ ∙ ¬-≃ (∸≤≃≤+ .fst) ((∸≤≃≤+ ⁻¹) .fst) ∙ <≃≱ ⁻¹

≤-∸-r-≃ : ∀ {m n p} → 0 < n → (n ≤ p ∸ m) ≃ (m + n ≤ p)
≤-∸-r-≃     {n = zero}      n>0 = false! n>0
≤-∸-r-≃ {m} {n = suc n} {p} n>0 = <≃suc≤ ∙ <-∸-r-≃ ∙ <≃suc≤ ⁻¹
                                ∙ subst (λ q → q ≤ p ≃ m + suc n ≤ p) (+-suc-r m n) refl

<-∸-l-≃ : ∀ {m n p} → 0 < p → (m ∸ n < p) ≃ (m < n + p)
<-∸-l-≃         {p = zero}  p>0 = absurd (≮z p>0)
<-∸-l-≃ {m} {n} {p = suc p} p>0 = <≃suc≤ ⁻¹ ∙ ≤≃≤+l {m = 1} ⁻¹ ∙ ∸≤≃≤+ {m} {n} ∙ ≤≃≤+l
                                ∙ subst (λ q → suc m ≤ q ≃ suc m ≤ n + suc p) (+-suc-r n p) refl ∙ <≃suc≤

opaque
  unfolding _≤_
  ≤→Σ : ∀ m n → m ≤ n → Σ[ k ꞉ ℕ ] (m + k ＝ n)
  ≤→Σ m n = id
