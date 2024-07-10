{-# OPTIONS --safe #-}
module Data.Nat.DivMod where

open import Foundations.Base
open import Foundations.Equiv
open import Meta.Marker
open import Data.Nat.Base renaming (div-helper to divₕ; mod-helper to modₕ)
open import Data.Nat.Path
open import Data.Nat.Order.Inductive
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Properties

infix 4 _∣_
infixl 7 _/_
infixl 7 _%_

-- division (rounding down)

_/_ : ℕ → ℕ → ℕ
m /  zero   = 0
m / (suc n) = divₕ 0 n m n

-- modulo

_%_ : ℕ → ℕ → ℕ
m %  zero   = m
m % (suc n) = modₕ 0 n m n

-- divisibility

record _∣_ (m n : ℕ) : 𝒰 where
  constructor divides
  field quot  : ℕ
        proof : n ＝ quot · m

-- properties

0-div-0 : ∀ n → 0 / n ＝ 0
0-div-0  zero   = refl
0-div-0 (suc n) = refl

div-mod-lemma : ∀ am ad d n
              → am + ad · suc (am + n) + d ＝ modₕ am (am + n) d n + divₕ ad (am + n) d n · suc (am + n)
div-mod-lemma am ad  zero    n      = +-zero-r (am + ad · suc (am + n))
div-mod-lemma am ad (suc d)  zero   =
    ap (λ q → am + ad · suc q + suc d) (+-zero-r am)
  ∙ +-suc-r (am + ad · suc am) d
  ∙ div-mod-lemma 0 (suc ad) d am
  ∙ ap (λ q → modₕ 0 q d q + divₕ (suc ad) q d q · suc q) (sym $ +-zero-r am)
div-mod-lemma am ad (suc d) (suc n) =
    ap (λ q → am + ad · suc q + suc d) (+-suc-r am n)
  ∙ +-suc-r (am + ad · suc (suc (am + n))) d
  ∙ div-mod-lemma (suc am) ad d n
  ∙ ap (λ q → modₕ (suc am) q d n + divₕ ad q d n · suc q) (sym $ +-suc-r am n)

modₕ-skipTo0 : ∀ acc n a b → modₕ acc n (b + a) a ＝ modₕ (a + acc) n b 0
modₕ-skipTo0 acc n  zero   b = ap (λ q → modₕ acc n q 0) (+-zero-r b)
modₕ-skipTo0 acc n (suc a) b =
    ap (λ q → modₕ acc n q (suc a)) (+-suc-r b a)
  ∙ modₕ-skipTo0 (suc acc) n a b
  ∙ ap (λ q → modₕ q n b 0) (+-suc-r a acc)

n[modₕ]n≡0 : ∀ acc v → modₕ acc (acc + v) (suc v) v ＝ 0
n[modₕ]n≡0 acc v = modₕ-skipTo0 acc (acc + v) v 1

a≤n⇒a[modₕ]n≡a : ∀ acc n a b → modₕ acc n a (a + b) ＝ acc + a
a≤n⇒a[modₕ]n≡a acc n  zero   b = sym (+-zero-r acc)
a≤n⇒a[modₕ]n≡a acc n (suc a) b = a≤n⇒a[modₕ]n≡a (suc acc) n a b ∙ sym (+-suc-r acc a)

m≡m%n+[m/n]*n : ∀ m n → m ＝ m % n + (m / n) · n
m≡m%n+[m/n]*n m  zero   = sym $ +-zero-r m
m≡m%n+[m/n]*n m (suc n) = div-mod-lemma 0 0 m n

m%n≡m∸m/n*n : ∀ m n → m % n ＝ m ∸ (m / n) · n
m%n≡m∸m/n*n m n =
  m % n
    ＝˘⟨ +-cancel-∸-r (m % n) ((m / n) · n ) ⟩
  m % n + m / n · n ∸ m / n · n
    ＝˘⟨ ap (_∸ m / n · n) (m≡m%n+[m/n]*n m n) ⟩
  m ∸ (m / n) · n
    ∎

[m/n]*n＝ : ∀ m n → (m / n) · n ＝ m ∸ m % n
[m/n]*n＝ m n = sym (+-cancel-∸-r (m / n · n) (m % n))
              ∙ ap (_∸ m % n) (+-comm (m / n · n) (m % n) ∙ sym (m≡m%n+[m/n]*n m n))

n%n＝0 : ∀ n → n % n ＝ 0
n%n＝0  zero   = refl
n%n＝0 (suc n) = n[modₕ]n≡0 0 n

∣-is-prop : ∀ m n → m ≠ 0 → is-prop (m ∣ n)
∣-is-prop m n m≠0 = is-prop-η go
  where
  go : (p q : m ∣ n) → p ＝ q
  go (divides q₁ prf₁) (divides q₂ prf₂) =
    ap² divides
      ([ id , (λ m=0 → absurd (m≠0 m=0)) ]ᵤ (·-cancel-r q₁ q₂ m (sym prf₁ ∙ prf₂)))
      (to-pathᴾ (is-set-β ℕ-is-set n _ _ prf₂))

¬0∣suc : ∀ n → ¬ (0 ∣ suc n)
¬0∣suc n (divides q pf) = absurd (suc≠zero (pf ∙ ·-absorb-r q))

∣→≤ : ∀ m n → n ≠ 0 → m ∣ n → m ≤ n
∣→≤ m    zero     n≠0  mn                  = absurd (n≠0 refl)
∣→≤ m   (suc n)   n≠0 (divides  zero   pf) = absurd (suc≠zero pf)
∣→≤ m n@(suc n-1) n≠0 (divides (suc q) pf) = ≤-trans ≤-+-r (subst (_≤ n) pf ≤-refl)

∣-refl : ∀ n → n ∣ n
∣-refl n = divides 1 (sym $ ·-id-l n)

∣-trans : ∀ m n p → m ∣ n → n ∣ p → m ∣ p
∣-trans m n p (divides qm prfm) (divides qn prfn) =
  divides (qn · qm) (prfn ∙ ap (qn ·_) prfm ∙ ·-assoc qn qm m)

∣-antisym : ∀ m n → m ∣ n → n ∣ m → m ＝ n
∣-antisym  zero    n     (divides q prf) n∣m = sym (prf ∙ ·-absorb-r q)
∣-antisym (suc m)  zero   m∣n            n∣m = absurd (¬0∣suc m n∣m)
∣-antisym (suc m) (suc n) m∣n            n∣m =
  ≤-antisym (∣→≤ (suc m) (suc n) suc≠zero m∣n) (∣→≤ (suc n) (suc m) suc≠zero n∣m)

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides 0 refl

∣n∣m%n⇒∣m : ∀ {m n d} → d ∣ n → d ∣ m % n → d ∣ m
∣n∣m%n⇒∣m {m} {n} {d} (divides q prf) (divides qm prfm) =
  divides (qm + (m / n) · q)
    (m
      ＝⟨ m≡m%n+[m/n]*n m n ⟩
     ⌜ m % n ⌝ + m / n · n
      ＝⟨ ap! prfm ⟩
     qm · d + m / n · ⌜ n ⌝
      ＝⟨ ap! prf ⟩
     qm · d + ⌜ m / n · (q · d) ⌝
      ＝⟨ ap! (·-assoc (m / n) q d) ⟩
     qm · d + m / n · q · d
      ＝˘⟨ ·-distrib-+-r qm (m / n · q) d ⟩
    (qm + m / n · q) · d
      ∎)

%-presˡ-∣ : ∀ {m n d} → d ∣ m → d ∣ n → d ∣ m % n
%-presˡ-∣ {m} {n} {d} (divides qm prfm) (divides qn prfn) =
  divides (qm ∸ m / n · qn)
    (m % n
       ＝⟨ m%n≡m∸m/n*n m n ⟩
     m ∸ m / n · ⌜ n ⌝
       ＝⟨ ap! prfn ⟩       
     m ∸ ⌜ m / n · (qn · d) ⌝
       ＝⟨ ap! (·-assoc (m / n) qn d) ⟩       
     ⌜ m ⌝ ∸ m / n · qn · d
       ＝⟨ ap! prfm ⟩       
     qm · d ∸ m / n · qn · d
       ＝˘⟨ ·-distrib-∸-r qm (m / n · qn) d ⟩       
     (qm ∸ m / n · qn) · d
       ∎)
