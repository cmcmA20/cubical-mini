{-# OPTIONS --safe #-}
module Data.Fin.Computational.Closure where

open import Meta.Prelude

open import Meta.Marker
open import Meta.Regularity

open import Data.Bool.Base as Bool
open import Data.Empty.Base as ⊥
open import Data.Empty.Properties as ⊥
open import Data.Fin.Computational.Properties
open import Data.Nat.Base
open import Data.Nat.Order.Inductive.Base
open import Data.Reflects.Base
open import Data.Sum.Base as ⊎
open import Data.Sum.Properties as ⊎
open import Data.Unit.Base
open import Data.Unit.Properties as ⊤

private variable
  ℓ : Level
  @0 m n : ℕ

fin-0-is-initial : Fin 0 ≃ ⊥
fin-0-is-initial = ¬→≃⊥ false!

fin-1-is-contr : is-contr (Fin 1)
fin-1-is-contr .fst = fzero
fin-1-is-contr .snd (mk-fin 0) = refl

fin-suc : Fin (suc n) ≃ ⊤ ⊎ Fin n
fin-suc = ≅→≃ $ iso f g (fun-ext rinv) (fun-ext linv) where
  f : Fin (suc n) → ⊤ ⊎ Fin n
  f (mk-fin 0)       = inl tt
  f (mk-fin (suc k)) = inr (mk-fin k)
  g : ⊤ ⊎ Fin n → Fin (suc n)
  g (inl _) = fzero
  g (inr x) = fsuc x
  rinv : g section-of′ f
  rinv (inl _) = refl
  rinv (inr _) = refl
  linv : g retraction-of′ f
  linv (mk-fin 0)       = refl
  linv (mk-fin (suc _)) = refl

fin-suc-universal
  : {n : ℕ} → {A : Fin (suc n) → Type ℓ}
  → Π[ x ꞉ Fin (suc n) ] A x
  ≃ A fzero × (∀ x → A (fsuc x))
fin-suc-universal {n} {A} = ≅→≃ $ iso ff gg refl (fun-ext li) where
  ff : Π[ x ꞉ Fin _ ] A x → A fzero × (∀ x → A (fsuc x))
  ff f = f fzero , f ∘ fsuc

  gg : A fzero × (∀ x → A (fsuc x)) → Π[ x ꞉ Fin _ ] A x
  gg (z , f) (mk-fin 0)       = z
  gg (z , f) (mk-fin (suc k)) = f (mk-fin k)

  li : gg retraction-of′ ff
  li w = fun-ext λ where
    (mk-fin 0)       → refl
    (mk-fin (suc k)) → refl


fin-coproduct : {n m : ℕ}
              → Fin n ⊎ Fin m
              ≃ Fin (n + m)
fin-coproduct {0} {m}  =
  Fin 0 ⊎ Fin m  ~⟨ ⊎-ap-l fin-0-is-initial ⟩
  ⊥ ⊎ Fin m      ~⟨ ⊎-zero-l ⟩
  Fin m          ∎
fin-coproduct {suc n} {m} =
  Fin (suc n) ⊎ Fin m  ~⟨ ⊎-ap-l fin-suc ⟩
  (⊤ ⊎ Fin n) ⊎ Fin m  ~⟨ ⊎-assoc ⟩
  ⊤ ⊎ Fin n ⊎ Fin m    ~⟨ ⊎-ap-r (fin-coproduct {n} {m}) ⟩
  ⊤ ⊎ Fin (n + m)      ~⟨ fin-suc ⁻¹ ⟩
  Fin (suc (n + m))    ∎

sum : ∀ n → (Fin n → ℕ) → ℕ
sum zero    f = zero
sum (suc n) f = f fzero + sum n (f ∘ fsuc)

fin-sum : {n : ℕ} (B : Fin n → ℕ)
        → Σ[ k ꞉ Fin n ] Fin (B k)
        ≃ Fin (sum n B)
fin-sum {0} _ .fst ()
fin-sum {0} _ .snd .equiv-proof ()
fin-sum {suc n} B =
  fin-coproduct {n = B fzero} .fst ∘ f ,
  is-equiv-comp (qinv→is-equiv f-inv) (fin-coproduct {n = B fzero} .snd)
    where
      rec″ : Σ[ k ꞉ Fin n ] Fin (B (fsuc k)) ≃ Fin (sum n (B ∘ fsuc))
      rec″ = fin-sum {n = n} (B ∘ fsuc)
      module mrec = Equiv rec″

      f : Σ[ k ꞉ Fin (suc n) ] Fin (B k) → Fin (B fzero) ⊎ Fin (sum n (B ∘ fsuc))
      f (mk-fin 0       , x) = inl x
      f (mk-fin (suc k) , y) = inr (mrec.to (mk-fin k , y))

      f-inv : quasi-inverse f
      f-inv .quasi-inverse.inv (inl x) = fzero , x
      f-inv .quasi-inverse.inv (inr x) with mrec.from x
      ... | x , y = fsuc x , y
      f-inv .quasi-inverse.inverses .Inverses.inv-o i (inl x) = inl x
      f-inv .quasi-inverse.inverses .Inverses.inv-o i (inr x) = inr (mrec.ε i x)
      f-inv .quasi-inverse.inverses .Inverses.inv-i i (mk-fin 0 , s) = mk-fin 0 , s
      f-inv .quasi-inverse.inverses .Inverses.inv-i i (mk-fin (suc k) , s)
        = fsuc (fst (mrec.η (~ i) (mk-fin k , s)))
        , snd (mrec.η (~ i) (mk-fin k , s))

fin-product : {n m : ℕ}
            → Fin n × Fin m
            ≃ Fin (n · m)
fin-product {n} {m} =
  Fin n × Fin m          ~⟨ fin-sum (λ _ → m) ⟩
  Fin (sum n (λ _ → m))  ~⟨ =→≃ (ap (λ n → Fin n) (sum~* n m))  ⟩
  Fin (n · m)            ∎
  where
    sum~* : ∀ n m → sum n (λ _ → m) ＝ n · m
    sum~* 0       m = refl
    sum~* (suc n) m = ap (m +_) (sum~* n m)


fin-fun : {n m : ℕ}
        → (Fin n → Fin m)
        ≃ Fin (m ^ n)
fin-fun {0} {m} =
  (Fin 0 → Fin m)  ~⟨ Π-dom-≃ fin-0-is-initial ⟨
  (⊥ → Fin m)      ~⟨ ⊥.universal ⟩
  ⊤                ~⟨ is-contr→equiv-⊤ fin-1-is-contr ⟨
  Fin 1            ∎
fin-fun {suc n} {m} =
  (Fin (suc n) → Fin m)          ~⟨ Π-dom-≃ fin-suc ⟨
  (⊤ ⊎ Fin n → Fin m)            ~⟨ ⊎.universal ⟩
  (⊤ → Fin m) × (Fin n → Fin m)  ~⟨ ×-ap ⊤.universal fin-fun ⟩
  Fin m × Fin (m ^ n)            ~⟨ fin-product ⟩
  Fin (m · m ^ n)                ∎
