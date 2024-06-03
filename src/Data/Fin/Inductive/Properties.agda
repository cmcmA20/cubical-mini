{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Properties where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Data.Empty.Base as ⊥
open import Data.Nat.Path
open import Data.Nat.Order.Inductive
open import Data.Sum.Base as ⊎

open import Data.Fin.Inductive.Base public
open import Data.Fin.Inductive.Path

private variable
  ℓ : Level
  @0 m n : ℕ

cast : {m n : ℕ} (@0 p : m ＝ n) → Fin m → Fin n
cast {suc m} {0}     p _        = absurd $ suc≠zero p
cast {suc m} {suc n} _ fzero    = fzero
cast {suc m} {suc n} p (fsuc k) = fsuc $ cast (suc-inj p) k

cast-is-equiv : {m n : ℕ} (p : m ＝ n) → is-equiv (cast p)
cast-is-equiv = Jₚ (λ _ p → is-equiv (cast p)) cast-refl-is-equiv
  where
    id=cast-refl : {n : ℕ} → refl ＝ cast (λ _ → n)
    id=cast-refl {0}     _ ()
    id=cast-refl {suc n} _ fzero    = fzero
    id=cast-refl {suc n} i (fsuc k) = fsuc $ id=cast-refl i k

    cast-refl-is-equiv : {n : ℕ} → is-equiv (cast (λ _ → n))
    cast-refl-is-equiv = subst is-equiv id=cast-refl id-is-equiv

cast-equiv : {m n : ℕ} → m ＝ n → Fin m ≃ Fin n
cast-equiv p = cast p , cast-is-equiv p

strengthen : {n : ℕ} → Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen fzero            = inl fzero
strengthen {suc n} (fsuc x) = ⊎.dmap fsuc fsuc $ strengthen x

inject : m ≤ n → Fin m → Fin n
inject (s≤s _)  fzero    = fzero
inject (s≤s le) (fsuc x) = fsuc $ inject le x

fin-peel : Fin (suc m) ≃ Fin (suc n) → Fin m ≃ Fin n
fin-peel {m} {n} sm≃sn = ≅→≃ $ m→n , iso n→m b→a→b a→b→a where
  sn≃sm : Fin (suc n) ≃ Fin (suc m)
  sn≃sm = sm≃sn ⁻¹
  module sm≃sn = Equiv sm≃sn
  module sn≃sm = Equiv sn≃sm

  m→n : Fin m → Fin n
  m→n x with inspect (sm≃sn $ fsuc x)
  ... | fsuc y , _ = y
  ... | fzero , p with inspect (sm≃sn $ fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd $ fzero≠fsuc $ sm≃sn.injective₂ q p

  n→m : Fin n → Fin m
  n→m x with inspect (sn≃sm $ fsuc x)
  ... | fsuc x , _ = x
  ... | fzero , p with inspect (sn≃sm $ fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd $ fzero≠fsuc $ sn≃sm.injective₂ q p

  a→b→a : ∀ a → n→m (m→n a) ＝ a
  a→b→a a with inspect (sm≃sn $ fsuc a)
  a→b→a a | fsuc x , p′ with inspect (sn≃sm $ fsuc x)
  a→b→a a | fsuc x , p′ | fsuc y , q′ =
    fsuc-inj $ q′ ⁻¹ ∙ ap$ sn≃sm (p′ ⁻¹) ∙ sm≃sn.η _
  a→b→a a | fsuc x , p′ | fzero , q′ = absurd ctra where
    r = sm≃sn.injective₂ p′ $ sm≃sn.ε $ fsuc x
    ctra = fzero≠fsuc $ (r ∙ q′) ⁻¹
  a→b→a a | fzero , p′ with inspect (sm≃sn $ fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ with inspect (sn≃sm $ fsuc x)
  a→b→a a | fzero , p′ | fsuc x , q′ | fsuc y , r′ =
    absurd $ fzero≠fsuc $ sm≃sn.η fzero ⁻¹ ∙ ap$ sn≃sm q′ ∙ r′
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect (sn≃sm $ fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s =
    fsuc-inj $ s ⁻¹ ∙ ap$ sn≃sm (p′ ⁻¹) ∙ sm≃sn.η (fsuc a)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  a→b→a a | fzero , p′ | fzero , q′ = absurd $ fzero≠fsuc $ sm≃sn.injective₂ q′ p′

  b→a→b : ∀ b → m→n (n→m b) ＝ b
  b→a→b b with inspect (sn≃sm $ fsuc b)
  b→a→b b | fsuc x , p′ with inspect (sm≃sn $ fsuc x)
  b→a→b b | fsuc x , p′ | fsuc y , q′ =
    fsuc-inj $ (ap$ sm≃sn p′ ∙ q′) ⁻¹ ∙ sn≃sm.η _
  b→a→b b | fsuc x , p′ | fzero , q′ = absurd ctra where
    r = sn≃sm.injective₂ p′ $ sn≃sm.ε $ fsuc x
    ctra = fzero≠fsuc $ (r ∙ q′) ⁻¹
  b→a→b b | fzero , p′ with inspect (sn≃sm $ fzero)
  b→a→b b | fzero , p′ | fsuc x , q′ with inspect (sm≃sn $ fsuc x)
  b→a→b b | fzero , p′ | fsuc x , q′ | fsuc y , r′  =
    absurd $ fzero≠fsuc $ sn≃sm.η _ ⁻¹ ∙ ap$ sm≃sn q′ ∙ r′
  b→a→b b | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect (sm≃sn $ fzero)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s =
    fsuc-inj $ (ap$ sm≃sn p′ ∙ s) ⁻¹ ∙ sn≃sm.η (fsuc a)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  b→a→b b | fzero , p′ | fzero , q′ = absurd $ fzero≠fsuc $ sn≃sm.injective₂ q′ p′

fin-injective : {m n : ℕ} → Fin m ≃ Fin n → m ＝ n
fin-injective {0}     {0}     _ = refl
fin-injective {0}     {suc n} f = ⊥.rec $ fin0-is-initial $ f ⁻¹ $ fzero
fin-injective {suc m} {0}     f = ⊥.rec $ fin0-is-initial $ f $ fzero
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
