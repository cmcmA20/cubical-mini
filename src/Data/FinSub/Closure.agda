{-# OPTIONS --safe #-}
module Data.FinSub.Closure where

open import Foundations.Base
open import Foundations.Sigma
open import Foundations.Equiv
open import Foundations.Path
open import Foundations.Transport
open import Foundations.Univalence

open import Meta.Marker
open import Meta.Search.HLevel
open import Meta.Regularity

open import Correspondences.Erased

import      Data.Empty.Base as ⊥
open ⊥ using (⊥)
open import Data.Nat.Base
open import Data.Nat.Order.Computational
open import Data.Sum.Properties

open import Data.FinSub.Properties

private variable
  ℓ : Level
  @0 m n : ℕ

opaque
  unfolding Fin
  fin-0-is-initial : Fin 0 ≃ ⊥
  fin-0-is-initial .fst ()
  fin-0-is-initial .snd .equiv-proof ()

  opaque
    unfolding is-of-hlevel
    fin-1-is-contr : is-contr (Fin 1)
    fin-1-is-contr .fst = fzero
    fin-1-is-contr .snd (0 , _) = refl

  fin-suc : Fin (suc n) ≃ ⊤ ⊎ Fin n
  fin-suc = iso→equiv (f , iso g rinv linv) where
    f : Fin (suc n) → ⊤ ⊎ Fin n
    f (0 , _) = inl tt
    f (suc k , ∣ p ∣ᴱ) = inr $ k , ∣ p ∣ᴱ
    g : ⊤ ⊎ Fin n → Fin (suc n)
    g (inl _) = fzero
    g (inr x) = fsuc x
    rinv : g is-right-inverse-of f
    rinv (inl _) = refl
    rinv (inr x) = refl
    linv : g is-left-inverse-of f
    linv (0 , _) = refl
    linv (suc _ , _) = refl

  fin-suc-universal
    : {n : ℕ} → {A : Fin (suc n) → Type ℓ}
    → Π[ x ꞉ Fin (suc n) ] A x
    ≃ A fzero × (∀ x → A (fsuc x))
  fin-suc-universal {n} {A} = iso→equiv $ ff , iso gg ri li where
    ff : Π[ x ] A x → A fzero × (∀ x → A (fsuc x))
    ff f = f fzero , f ∘ fsuc

    gg : A fzero × (∀ x → A (fsuc x)) → Π[ x ] A x
    gg (z , f) (0 , _) = z
    gg (z , f) (suc k , ∣ p ∣ᴱ) = f $ k , ∣ p ∣ᴱ

    ri : gg is-right-inverse-of ff
    ri _ = refl

    li : gg is-left-inverse-of ff
    li w = fun-ext λ where
      (0 , ∣ p ∣ᴱ) → refl
      (suc k , p) → refl


fin-coproduct : {n m : ℕ}
              → Fin n ⊎ Fin m
              ≃ Fin (n + m)
fin-coproduct {0} {m}  =
  Fin 0 ⊎ Fin m ≃⟨ ⊎-ap-l fin-0-is-initial ⟩
  ⊥ ⊎ Fin m     ≃⟨ ⊎-zero-l ⟩
  Fin m         ≃∎
fin-coproduct {suc n} {m} =
  Fin (suc n) ⊎ Fin m ≃⟨ ⊎-ap-l fin-suc ⟩
  (⊤ ⊎ Fin n) ⊎ Fin m ≃⟨ ⊎-assoc ⟩
  ⊤ ⊎ Fin n ⊎ Fin m   ≃⟨ ⊎-ap-r (fin-coproduct {n} {m}) ⟩
  ⊤ ⊎ Fin (n + m)     ≃⟨ fin-suc ₑ⁻¹ ⟩
  Fin (suc (n + m))   ≃∎

sum : ∀ n → (Fin n → ℕ) → ℕ
sum zero    f = zero
sum (suc n) f = f fzero + sum n (f ∘ fsuc)

opaque
  unfolding Fin
  fin-sum : {n : ℕ} (B : Fin n → ℕ)
          → Σ[ k ꞉ Fin n ] Fin (B k)
          ≃ Fin (sum n B)
  fin-sum {0} _ .fst ()
  fin-sum {0} _ .snd .equiv-proof ()
  fin-sum {suc n} B =
    fin-coproduct {n = B fzero} .fst ∘ f ,
    is-equiv-comp (is-iso→is-equiv $ f-iso) (fin-coproduct {n = B fzero} .snd)
      where
        rec′ : Σ[ k ꞉ Fin n ] Fin (B (fsuc k)) ≃ Fin (sum n (B ∘ fsuc))
        rec′ = fin-sum {n = n} (B ∘ fsuc)
        module mrec = Equiv rec′

        f : Σ[ k ꞉ Fin (suc n) ] Fin (B k) → Fin (B fzero) ⊎ Fin (sum n (B ∘ fsuc))
        f ((0 , _) , x) = inl x
        f ((suc k , p) , y) = inr (mrec.to ((k , p) , y))

        f-iso : is-iso f
        f-iso .is-iso.inv (inl x) = fzero , x
        f-iso .is-iso.inv (inr x) with mrec.from x
        ... | x , y = fsuc x , y

        f-iso .is-iso.rinv (inl x) = refl
        f-iso .is-iso.rinv (inr x) = ap inr (mrec.ε _)

        f-iso .is-iso.linv ((zero , _) , _) = refl
        f-iso .is-iso.linv ((suc k , p) , y) =
          Σ-pathP (ap (fsuc ∘ fst) (mrec.η _)) (ap snd (mrec.η _))


fin-product : {n m : ℕ}
            → Fin n × Fin m
            ≃ Fin (n · m)
fin-product {n} {m} =
  Fin n × Fin m         ≃⟨ fin-sum {n = n} (λ _ → m) ⟩
  Fin (sum n (λ _ → m)) ≃⟨ path→equiv (ap (λ n → Fin n) (sum≡* n m))  ⟩
  Fin (n · m)           ≃∎
  where
    sum≡* : ∀ n m → sum n (λ _ → m) ＝ n · m
    sum≡* zero m = refl
    sum≡* (suc n) m = ap (m +_) (sum≡* n m)
