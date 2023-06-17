{-# OPTIONS --safe #-}
module Data.Fin.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind

open import Data.Empty.Base
open import Data.Nat.Path
open import Data.Nat.Order
import      Data.Sum.Base as ⊎
open ⊎

open import Data.Fin.Base public

private variable
  ℓ : Level
  @0 m n : ℕ

cast : {m n : ℕ} → m ＝ n → Fin m → Fin n
cast {suc m} {0}     p _        = absurd (suc≠zero p)
cast {suc m} {suc n} _ fzero    = fzero
cast {suc m} {suc n} p (fsuc k) = fsuc $ cast (suc-inj p) k

cast-is-equiv : {m n : ℕ} (p : m ＝ n) → is-equiv (cast p)
cast-is-equiv = J (λ _ p → is-equiv (cast p)) cast-refl-is-equiv
  where
    id=cast-refl : {n : ℕ} → id ＝ cast (λ _ → n)
    id=cast-refl {0}     _ ()
    id=cast-refl {suc n} _ fzero = fzero
    id=cast-refl {suc n} i (fsuc k) = fsuc $ id=cast-refl i k

    cast-refl-is-equiv : {n : ℕ} → is-equiv (cast (λ _ → n))
    cast-refl-is-equiv = subst is-equiv id=cast-refl id-is-equiv

cast-equiv : {m n : ℕ} → m ＝ n → Fin m ≃ Fin n
cast-equiv p = cast p , cast-is-equiv p

strengthen : {n : ℕ} → Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen fzero    = inl fzero
strengthen {suc n} (fsuc x) = ⊎.map fsuc fsuc $ strengthen x

inject : m ≤ n → Fin m → Fin n
inject (s≤s _)  fzero    = fzero
inject (s≤s le) (fsuc x) = fsuc $ inject le x

fzero≠fsuc : {k : Fin m} → ¬ fzero ＝ fsuc k
fzero≠fsuc p = subst discrim p tt where
  discrim : Fin (suc m) → Type
  discrim fzero    = ⊤
  discrim (fsuc _) = ⊥

fsuc-inj : {k l : Fin m} → fsuc k ＝ fsuc l → k ＝ l
fsuc-inj {k} = ap pred′ where
  pred′ : Fin (suc _) → Fin _
  pred′ fzero    = k
  pred′ (fsuc x) = x

fin-peel : Fin (suc m) ≃ Fin (suc n) → Fin m ≃ Fin n
fin-peel {m} {n} sm≃sn = iso→equiv $ m→n , iso n→m b→a→b a→b→a where
  sn≃sm : Fin (suc n) ≃ Fin (suc m)
  sn≃sm = sm≃sn ₑ⁻¹
  module sm≃sn = Equiv sm≃sn
  module sn≃sm = Equiv sn≃sm

  m→n : Fin m → Fin n
  m→n x with inspect $ sm≃sn.to $ fsuc x
  ... | fsuc y , _ = y
  ... | fzero , p with inspect $ sm≃sn.to fzero
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc $ sm≃sn.injective₂ q p)

  n→m : Fin n → Fin m
  n→m x with inspect $ sn≃sm.to $ fsuc x
  ... | fsuc x , _ = x
  ... | fzero , p with inspect $ sn≃sm.to fzero
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc $ sn≃sm.injective₂ q p)

  a→b→a : ∀ a → n→m (m→n a) ＝ a
  a→b→a a with inspect $ sm≃sn.to $ fsuc a
  a→b→a a | fsuc x , p′ with inspect $ sn≃sm.to $ fsuc x
  a→b→a a | fsuc x , p′ | fsuc y , q′ =
    fsuc-inj $ sym q′ ∙ ap (sn≃sm.to) (sym p′) ∙ sm≃sn.η _
  a→b→a a | fsuc x , p′ | fzero , q′ = absurd contra where
    r = sm≃sn.injective₂ p′ $ sm≃sn.ε $ fsuc x
    contra = fzero≠fsuc $ sym $ r ∙ q′
  a→b→a a | fzero , p′ with inspect $ sm≃sn.to fzero
  a→b→a a | fzero , p′ | fsuc x , q′ with inspect $ sn≃sm.to $ fsuc x
  a→b→a a | fzero , p′ | fsuc x , q′ | fsuc y , r′ =
    absurd (fzero≠fsuc $ sym $ sym r′ ∙ ap sn≃sm.to (sym q′) ∙ sm≃sn.η fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect $ sn≃sm.to fzero
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s =
    fsuc-inj $ sym s ∙ ap sn≃sm.to (sym p′) ∙ sm≃sn.η (fsuc a)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  a→b→a a | fzero , p′ | fzero , q′ = absurd (fzero≠fsuc $ sm≃sn.injective₂ q′ p′)

  b→a→b : ∀ b → m→n (n→m b) ＝ b
  b→a→b b with inspect $ sn≃sm.to $ fsuc b
  b→a→b b | fsuc x , p′ with inspect $ sm≃sn.to $ fsuc x
  b→a→b b | fsuc x , p′ | fsuc y , q′ =
    fsuc-inj $ sym q′ ∙ ap (sm≃sn.to) (sym p′) ∙ sn≃sm.η _
  b→a→b b | fsuc x , p′ | fzero , q′ = absurd contra where
    r = sn≃sm.injective₂ p′ $ sn≃sm.ε $ fsuc x
    contra = fzero≠fsuc $ sym $ r ∙ q′
  b→a→b b | fzero , p′ with inspect $ sn≃sm.to fzero
  b→a→b b | fzero , p′ | fsuc x , q′ with inspect $ sm≃sn.to $ fsuc x
  b→a→b b | fzero , p′ | fsuc x , q′ | fsuc y , r′  =
    absurd (fzero≠fsuc $ sym $ sym r′ ∙ ap (sm≃sn.to) (sym q′) ∙ sn≃sm.η _)
  b→a→b b | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect $ sm≃sn.to fzero
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s =
    fsuc-inj $ sym s ∙ ap (sm≃sn.to) (sym p′) ∙ sn≃sm.η (fsuc a)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  b→a→b b | fzero , p′ | fzero , q′ = absurd (fzero≠fsuc $ sn≃sm.injective₂ q′ p′)

fin-injective : {m n : ℕ} → Fin m ≃ Fin n → m ＝ n
fin-injective {0} {0}     _ = refl
fin-injective {0} {suc n} f with is-equiv→inverse (f .snd) fzero
... | ()
fin-injective {suc m} {0}     f with f .fst fzero
... | ()
fin-injective {suc m} {suc n} f = ap suc $ fin-injective (fin-peel f)

fin-choice
  : ∀ n {A : Fin n → Type ℓ} {M}
      (let module M = Effect M)
  → ⦃ Bind M ⦄
  → (∀ x → M.₀ (A x)) → M.₀ (∀ x → A x)
fin-choice zero _    = pure λ { () }
fin-choice (suc n) k = do
  azero ← k fzero
  asuc  ← fin-choice n (k ∘ fsuc)
  pure λ where
    fzero    → azero
    (fsuc x) → asuc x
