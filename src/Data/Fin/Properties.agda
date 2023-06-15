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
  m n : ℕ

cast : m ＝ n → Fin m → Fin n
cast {suc m} {(zero)} p _ = absurd (suc≠zero p)
cast {suc m} {suc n}  _ fzero    = fzero
cast {suc m} {suc n}  p (fsuc k) = fsuc (cast (suc-inj p) k)

cast-is-equiv : (p : m ＝ n) → is-equiv (cast p)
cast-is-equiv = J (λ _ p → is-equiv (cast p)) cast-refl-is-equiv
  where
    id＝cast-refl : id ＝ cast (λ _ → n)
    id＝cast-refl {(zero)} _ ()
    id＝cast-refl {suc n} _ fzero = fzero
    id＝cast-refl {suc n} i (fsuc k) = fsuc (id＝cast-refl i k)

    cast-refl-is-equiv : is-equiv (cast (λ _ → n))
    cast-refl-is-equiv = subst is-equiv id＝cast-refl id-is-equiv

cast-equiv : m ＝ n → Fin m ≃ Fin n
cast-equiv p = cast p , cast-is-equiv p

strengthen : Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen {(zero)} fzero = inl fzero
strengthen {suc n}  fzero = inr fzero
strengthen {suc n}  (fsuc k) = ⊎.map fsuc fsuc (strengthen k)

inject : m ≤ n → Fin m → Fin n
inject {_} {suc n} le       fzero    = fzero
inject {_} {suc n} (s≤s le) (fsuc k) = fsuc (inject le k)

fzero≠fsuc : {k : Fin m} → ¬ fzero ＝ fsuc k
fzero≠fsuc p = subst discrim p tt where
  discrim : Fin (suc m) → Type
  discrim fzero    = ⊤
  discrim (fsuc _) = ⊥

fsuc-inj : {k l : Fin m} → fsuc k ＝ fsuc l → k ＝ l
fsuc-inj {m = suc m} p = ap pred′ p
  where
    pred′ : Fin (suc (suc m)) → Fin (suc m)
    pred′ fzero    = fzero
    pred′ (fsuc _) = _

fin-peel : ∀ {l k} → Fin (suc l) ≃ Fin (suc k) → Fin l ≃ Fin k
fin-peel {l} {k} sl≃sk = iso→equiv (l→k , (iso k→l b→a→b a→b→a)) where
  sk≃sl : Fin (suc k) ≃ Fin (suc l)
  sk≃sl = sl≃sk ₑ⁻¹
  module sl≃sk = Equiv sl≃sk
  module sk≃sl = Equiv sk≃sl

  l→k : Fin l → Fin k
  l→k x with inspect (sl≃sk.to (fsuc x))
  ... | fsuc y , _ = y
  ... | fzero , p with inspect (sl≃sk.to fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc (sl≃sk.injective₂ q p))

  k→l : Fin k → Fin l
  k→l x with inspect (sk≃sl.to (fsuc x))
  ... | fsuc x , _ = x
  ... | fzero , p with inspect (sk≃sl.to fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc (sk≃sl.injective₂ q p))

  a→b→a : ∀ a → k→l (l→k a) ＝ a
  a→b→a a with inspect (sl≃sk.to (fsuc a))
  a→b→a a | fsuc x , p′ with inspect (sk≃sl.to (fsuc x))
  a→b→a a | fsuc x , p′ | fsuc y , q′ = fsuc-inj (
    sym q′ ∙ ap (sk≃sl.to) (sym p′) ∙ sl≃sk.η _)
  a→b→a a | fsuc x , p′ | fzero , q′ = absurd contra where
    r = sl≃sk.injective₂ p′ (sl≃sk.ε (fsuc x))
    contra = fzero≠fsuc (sym (r ∙ q′))
  a→b→a a | fzero , p′ with inspect (sl≃sk.to fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ with inspect (sk≃sl.to (fsuc x))
  a→b→a a | fzero , p′ | fsuc x , q′ | fsuc y , r′ =
    absurd (fzero≠fsuc (sym (sym r′ ∙ ap sk≃sl.to (sym q′) ∙ sl≃sk.η fzero)))
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect (sk≃sl.to fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s = fsuc-inj $
    sym s ∙ ap sk≃sl.to (sym p′) ∙ sl≃sk.η (fsuc a)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  a→b→a a | fzero , p′ | fzero , q′ =
    absurd (fzero≠fsuc $ sl≃sk.injective₂ q′ p′)

  b→a→b : ∀ b → l→k (k→l b) ＝ b
  b→a→b b with inspect (sk≃sl.to (fsuc b))
  b→a→b b | fsuc x , p′ with inspect (sl≃sk.to (fsuc x))
  b→a→b b | fsuc x , p′ | fsuc y , q′ = fsuc-inj $
    sym q′ ∙ ap (sl≃sk.to) (sym p′) ∙ sk≃sl.η _
  b→a→b b | fsuc x , p′ | fzero , q′ = absurd contra where
    r = sk≃sl.injective₂ p′ (sk≃sl.ε (fsuc x))
    contra = fzero≠fsuc (sym (r ∙ q′))
  b→a→b b | fzero , p′ with inspect (sk≃sl.to fzero)
  b→a→b b | fzero , p′ | fsuc x , q′ with inspect (sl≃sk.to (fsuc x))
  b→a→b b | fzero , p′ | fsuc x , q′ | fsuc y , r′  =
    absurd (fzero≠fsuc $ sym (sym r′ ∙ ap (sl≃sk.to) (sym q′) ∙ sk≃sl.η _))
  b→a→b b | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect (sl≃sk.to fzero)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s = fsuc-inj $
    sym s ∙ ap (sl≃sk.to) (sym p′) ∙ sk≃sl.η (fsuc a)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  b→a→b b | fzero , p′ | fzero , q′ =
    absurd (fzero≠fsuc $ sk≃sl.injective₂ q′ p′)

fin-injective : Fin m ≃ Fin n → m ＝ n
fin-injective {(zero)} {(zero)} _ = refl
fin-injective {(zero)} {suc n}  f with is-equiv→inverse (f .snd) fzero
... | ()
fin-injective {suc m} {(zero)}  f with f .fst fzero
... | ()
fin-injective {suc m} {suc n}   f = ap suc $ fin-injective (fin-peel f)

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
