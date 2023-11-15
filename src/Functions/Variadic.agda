{-# OPTIONS --safe #-}
module Functions.Variadic where

open import Foundations.Base

open import Data.Nat.Base

private variable
  ℓ ℓ′ a b c : Level
  n : ℕ
  A : Type a
  B : Type b
  C : Type c

Levels : ℕ → Type
Levels 0             = ⊤
Levels 1             = Level
Levels (suc (suc n)) = Level × Levels (suc n)

ℓsup : ∀ n → Levels n → Level
ℓsup 0             _        = 0ℓ
ℓsup 1             l        = l
ℓsup (suc (suc n)) (l , ls) = l ⊔ ℓsup _ ls

ℓreplicate : ∀ n → Level → Levels n
ℓreplicate 0             _ = _
ℓreplicate 1             ℓ = ℓ
ℓreplicate (suc (suc n)) ℓ = ℓ , ℓreplicate _ ℓ

Types : ∀ n (ls : Levels n) → Type (ℓsuc (ℓsup n ls))
Types 0             _        = Lift _ ⊤
Types 1             l        = Type l
Types (suc (suc n)) (l , ls) = Type l × Types _ ls

Arrows : ∀ n {ℓ ls} → Types n ls → Type ℓ → Type (ℓ ⊔ ℓsup n ls)
Arrows 0             _        B = B
Arrows 1             A        B = A → B
Arrows (suc (suc n)) (A , As) B = A → Arrows _ As B

funⁿ : ∀ {n ℓ ls} → Types n ls → Type ℓ → Type (ℓ ⊔ ℓsup n ls)
funⁿ = Arrows _

infixr -1 _<$>ⁿ_
_<$>ⁿ_ : (∀ {ℓ} → Type ℓ → Type ℓ)
       → ∀ {n ls} → Types n ls → Types n ls
_<$>ⁿ_ F {n = 0}           _        = _
_<$>ⁿ_ F {n = 1}           A        = A
_<$>ⁿ_ F {n = suc (suc n)} (A , As) = F A , (F <$>ⁿ As)

ℓmap : (Level → Level) → ∀ n → Levels n → Levels n
ℓmap f 0             _        = _
ℓmap f 1             l        = f l
ℓmap f (suc (suc n)) (l , ls) = f l , ℓmap f _ ls

ℓsmap : (f : Level → Level)
      → (∀ {ℓ} → Type ℓ → Type (f ℓ))
      → ∀ n {ls}
      → Types n ls → Types n (ℓmap f n ls)
ℓsmap _ _ 0             _        = _
ℓsmap _ F 1             A        = F A
ℓsmap f F (suc (suc n)) (A , As) = F A , ℓsmap f F _ As

-- mapping under n arguments
mapⁿ : ∀ n {ls} {As : Types n ls} → (B → C) → funⁿ As B → funⁿ As C
mapⁿ 0             f v = f v
mapⁿ 1             f v = f ∘′ v
mapⁿ (suc (suc n)) f g = mapⁿ _ f ∘′ g

-- compose function at the n-th position
infix 1 _%=_⊢_
_%=_⊢_ : ∀ n {ls} {As : Types n ls} → (A → B) → funⁿ As (B → C) → funⁿ As (A → C)
n %= f ⊢ g = mapⁿ n (_∘′ f) g

-- partially apply function at the n-th position
infix 1 _∷=_⊢_
_∷=_⊢_ : ∀ n {ls} {As : Types n ls} → A → funⁿ As (A → B) → funⁿ As B
n ∷= x ⊢ g = mapⁿ n (_$ x) g

-- hole at the n-th position
holeⁿ : ∀ n {ls} {As : Types n ls} → (A → funⁿ As B) → funⁿ As (A → B)
holeⁿ 0             f = f
holeⁿ 1             f = flip f
holeⁿ (suc (suc n)) f = holeⁿ _ ∘′ flip f

constⁿ : ∀ n {ls ℓ} {As : Types n ls} {B : Type ℓ} → B → funⁿ As B
constⁿ 0             v = v
constⁿ 1             v = λ _ → v
constⁿ (suc (suc n)) v = λ _ → constⁿ _ v


-- ℓhsup : ℕ → Level → Level → Level
-- ℓhsup 0       _  ℓ₂ = ℓ₂
-- ℓhsup (suc n) ℓ₁ ℓ₂ = ℓ₁ ⊔ ℓhsup n ℓ₁ ℓ₂

-- HArrows : (n : ℕ) → Type a → Type b → Type (ℓhsup n a b)
-- HArrows 0       _ B = B
-- HArrows (suc n) A B = A → HArrows n A B

-- hfunⁿ : ∀ {n} → Type a → Type b → Type (ℓhsup n a b)
-- hfunⁿ {n} = HArrows n

-- hmapⁿ : (n : ℕ) → (B → C) → hfunⁿ {n = n} A B → hfunⁿ {n = n} A C
-- hmapⁿ 0       f v = f v
-- hmapⁿ (suc n) f g = hmapⁿ _ f ∘′ g
