{-# OPTIONS --safe #-}
module Data.HVec.Base where

open import Foundations.Base

open import Data.Nat.Base

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ : Level
  n : ℕ
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ

Vec′ : Type ℓ → (n : ℕ) → Type ℓ
Vec′ _ 0 = Lift _ ⊤
Vec′ A 1 = A
Vec′ A (suc (suc n)) = A × Vec′ A (suc n)

Levels : ℕ → Type
Levels = Vec′ Level

ℓsup : ∀ n → Levels n → Level
ℓsup 0 _ = 0ℓ
ℓsup 1 l = l
ℓsup (suc (suc n)) (l , ls) = l ⊔ ℓsup _ ls

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

HVec : ∀ n {ls} → Types n ls → Type (ℓsup n ls)
HVec 0             _        = ⊤
HVec 1             A        = A
HVec (suc (suc n)) (A , As) = A × HVec (suc n) As

-- rec
uncurryⁿ : ∀ n {ls} {As : Types n ls} → funⁿ As B → HVec n As → B
uncurryⁿ 0             f          = λ _ → f
uncurryⁿ 1             f          = f
uncurryⁿ (suc (suc n)) f (a , as) = uncurryⁿ (suc n) (f a) as

infixr -1 _$ⁿ_
_$ⁿ_ : ∀ {n ls} {As : Types n ls} → funⁿ As B → HVec n As → B
_$ⁿ_ = uncurryⁿ _

curryⁿ : ∀ n {ls} {As : Types n ls} {ℓ} {B : Type ℓ}
       → (HVec n As → B) → funⁿ As B
curryⁿ 0             f = f _
curryⁿ 1             f = f
curryⁿ (suc (suc n)) f = curryⁿ (suc n) ∘′ curry² f