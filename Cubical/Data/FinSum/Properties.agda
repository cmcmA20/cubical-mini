{-# OPTIONS --safe #-}

module Cubical.Data.FinSum.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.FinSubtype as Fin
import Cubical.Data.FinSubtype.LehmerCode as LehmerCode
open import Cubical.Data.FinSum.Base as FinSum
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Truncation.Propositional as Prop

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Negation

private
  variable
    ℓ : Level
    k : ℕ

FinSum→Fin : Fin k → Fin.Fin k
FinSum→Fin = FinSum.elim (λ {k} _ → Fin.Fin k) Fin.fzero Fin.fsuc

Fin→FinSum : Fin.Fin k → Fin k
Fin→FinSum = Fin.elim (λ {k} _ → Fin k) fzero fsuc

Fin→FinSum-fsuc : (fk : Fin.Fin k) → Fin→FinSum (Fin.fsuc fk) ≡ fsuc (Fin→FinSum fk)
Fin→FinSum-fsuc = Fin.elim-fsuc (λ {k} _ → Fin k) fzero fsuc

FinSum→Fin→FinSum : (fk : Fin k) → Fin→FinSum (FinSum→Fin fk) ≡ fk
FinSum→Fin→FinSum = FinSum.elim (λ fk → Fin→FinSum (FinSum→Fin fk) ≡ fk)
                                refl λ {k} {fk} eq →
  Fin→FinSum (Fin.fsuc (FinSum→Fin fk)) ≡⟨ Fin→FinSum-fsuc (FinSum→Fin fk) ⟩
  fsuc (Fin→FinSum (FinSum→Fin fk))     ≡⟨ cong fsuc eq ⟩
  fsuc fk                               ∎

Fin→FinSum→Fin : (fk : Fin.Fin k) → FinSum→Fin (Fin→FinSum fk) ≡ fk
Fin→FinSum→Fin = Fin.elim (λ fk → FinSum→Fin (Fin→FinSum fk) ≡ fk)
                          refl λ {k} {fk} eq →
  FinSum→Fin (Fin→FinSum (Fin.fsuc fk)) ≡⟨ cong FinSum→Fin (Fin→FinSum-fsuc fk) ⟩
  Fin.fsuc (FinSum→Fin (Fin→FinSum fk)) ≡⟨ cong Fin.fsuc eq ⟩
  Fin.fsuc fk                           ∎

FinSum≃Fin : ∀ k → Fin k ≃ Fin.Fin k
FinSum≃Fin _ =
  isoToEquiv (iso FinSum→Fin Fin→FinSum Fin→FinSum→Fin FinSum→Fin→FinSum)

@0 FinSum≡Fin : ∀ k → Fin k ≡ Fin.Fin k
FinSum≡Fin k = ua (FinSum≃Fin k)

enum : (n : ℕ)(p : n < k) → Fin k
enum n p = Fin→FinSum (n , p)

enumElim : (P : Fin k → Type ℓ) → ((n : ℕ)(p : n < k) → P (enum _ p)) → (i : Fin k) → P i
enumElim P f i = subst P (FinSum→Fin→FinSum i) (f (FinSum→Fin i .fst) (FinSum→Fin i .snd))

-- Closure properties of FinSum under type constructors

FinSum⊎≃ : (m n : ℕ) → (Fin m ⊎ Fin n) ≃ (Fin (m + n))
FinSum⊎≃ 0 n = ⊎-swap-≃ ⋆ ⊎-⊥-≃
FinSum⊎≃ (suc m) n = ⊎-assoc-≃ ⋆ ⊎-equiv (idEquiv ⊤) (FinSum⊎≃ m n)

FinSumΣ≃ : (n : ℕ)(f : Fin n → ℕ) → (Σ (Fin n) (λ x → Fin (f x))) ≃ (Fin (totalSum f))
FinSumΣ≃ 0 f = ΣEmpty _
FinSumΣ≃ (suc n) f =
    Σ⊎≃
  ⋆ ⊎-equiv (ΣUnit (λ tt → Fin (f (inl tt)))) (FinSumΣ≃ n (λ x → f (inr x)))
  ⋆ FinSum⊎≃ (f (inl tt)) (totalSum (λ x → f (inr x)))

FinSum×≃ : (m n : ℕ) → (Fin m × Fin n) ≃ (Fin (m · n))
FinSum×≃ m n = FinSumΣ≃ m (λ _ → n) ⋆ pathToEquiv (λ i → Fin (totalSumConst {m = m} n i))

FinSumΠ≃ : (n : ℕ)(f : Fin n → ℕ) → ((x : Fin n) → Fin (f x)) ≃ (Fin (totalProd f))
FinSumΠ≃ 0 _ = isContr→≃Unit (isContrΠ⊥) ⋆ invEquiv (⊎-⊥-≃)
FinSumΠ≃ (suc n) f =
    Π⊎≃
  ⋆ Σ-cong-equiv (ΠUnit (λ tt → Fin (f (inl tt)))) (λ _ → FinSumΠ≃ n (λ x → f (inr x)))
  ⋆ FinSum×≃ (f (inl tt)) (totalProd (λ x → f (inr x)))

isNotZero : ℕ → ℕ
isNotZero 0 = 0
isNotZero (suc n) = 1

FinSum∥∥≃ : (n : ℕ) → ∥ Fin n ∥₁ ≃ Fin (isNotZero n)
FinSum∥∥≃ 0 = propTruncIdempotent≃ (isProp⊥)
FinSum∥∥≃ (suc n) =
    isContr→≃Unit (inhProp→isContr ∣ inl tt ∣₁ isPropPropTrunc)
  ⋆ isContr→≃Unit (isContrUnit) ⋆ invEquiv (⊎-⊥-≃)

ℕ→Bool : ℕ → Bool
ℕ→Bool 0 = false
ℕ→Bool (suc n) = true

FinSum∥∥DecProp : (n : ℕ) → ∥ Fin n ∥₁ ≃ Bool→Type (ℕ→Bool n)
FinSum∥∥DecProp 0 = uninhabEquiv (Prop.rec isProp⊥ (λ x → ⊥.rec x)) (λ x → ⊥.rec x)
FinSum∥∥DecProp (suc n) = isContr→≃Unit (inhProp→isContr ∣ inl tt ∣₁ isPropPropTrunc)

-- negation of FinSum

FinSum¬ : (n : ℕ) → (¬ Fin n) ≃ Bool→Type (isZero n)
FinSum¬ 0 = isContr→≃Unit isContr⊥→A
FinSum¬ (suc n) = uninhabEquiv (λ f → f fzero) (λ x → ⊥.rec x)

-- FinSum 1 is equivalent to unit

Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = ⊎-⊥-≃

isContrFinSum1 : isContr (Fin 1)
isContrFinSum1 = isOfHLevelRespectEquiv 0 (invEquiv Fin1≃Unit) isContrUnit

-- FinSum 2 is equivalent to Bool

FinSum2≃Bool : Fin 2 ≃ Bool
FinSum2≃Bool = ⊎-equiv (idEquiv _) ⊎-⊥-≃ ⋆ isoToEquiv Iso-⊤⊎⊤-Bool

-- decidable predicate over FinSum

FinSumℙ≃ : (n : ℕ) → (Fin n → Bool) ≃ Fin (2 ^ n)
FinSumℙ≃ 0 = isContr→≃Unit (isContrΠ⊥) ⋆ invEquiv (⊎-⊥-≃)
FinSumℙ≃ (suc n) =
    Π⊎≃
  ⋆ Σ-cong-equiv (UnitToType≃ Bool ⋆ invEquiv FinSum2≃Bool) (λ _ → FinSumℙ≃ n)
  ⋆ FinSum×≃ 2 (2 ^ n)

-- decidable subsets of FinSum

Bool→ℕ : Bool → ℕ
Bool→ℕ true = 1
Bool→ℕ false = 0

trueCount : {n : ℕ}(f : Fin n → Bool) → ℕ
trueCount {n = 0} _ = 0
trueCount {n = suc n} f = Bool→ℕ (f (inl tt)) + (trueCount (f ∘ inr))

FinSumDec⊎≃ : (n : ℕ)(t : Bool) → (Bool→Type t ⊎ Fin n) ≃ (Fin (Bool→ℕ t + n))
FinSumDec⊎≃ _ true = idEquiv _
FinSumDec⊎≃ _ false = ⊎-swap-≃ ⋆ ⊎-⊥-≃

FinSumSub≃ : (n : ℕ)(f : Fin n → Bool) → Σ _ (Bool→Type ∘ f) ≃ Fin (trueCount f)
FinSumSub≃ 0 _ = ΣEmpty _
FinSumSub≃ (suc n) f =
    Σ⊎≃
  ⋆ ⊎-equiv (ΣUnit (Bool→Type ∘ f ∘ inl)) (FinSumSub≃ n (f ∘ inr))
  ⋆ FinSumDec⊎≃ _ (f (inl tt))

-- decidable quantifier

trueForSome : (n : ℕ)(f : Fin n → Bool) → Bool
trueForSome 0 _ = false
trueForSome (suc n) f = f (inl tt) or trueForSome n (f ∘ inr)

trueForAll : (n : ℕ)(f : Fin n → Bool) → Bool
trueForAll 0 _ = true
trueForAll (suc n) f = f (inl tt) and trueForAll n (f ∘ inr)

FinSum∃→ : (n : ℕ)(f : Fin n → Bool) → Σ _ (Bool→Type ∘ f) → Bool→Type (trueForSome n f)
FinSum∃→ 0 _ = ΣEmpty _ .fst
FinSum∃→ (suc n) f =
    Bool→Type⊎' _ _
  ∘ map-⊎ (ΣUnit (Bool→Type ∘ f ∘ inl) .fst) (FinSum∃→ n (f ∘ inr))
  ∘ Σ⊎≃ .fst

FinSum∃← : (n : ℕ)(f : Fin n → Bool) → Bool→Type (trueForSome n f) → Σ _ (Bool→Type ∘ f)
FinSum∃← 0 _ p = ⊥.rec p
FinSum∃← (suc n) f =
    invEq Σ⊎≃
  ∘ map-⊎ (invEq (ΣUnit (Bool→Type ∘ f ∘ inl))) (FinSum∃← n (f ∘ inr))
  ∘ Bool→Type⊎ _ _

FinSum∃≃ : (n : ℕ)(f : Fin n → Bool) → ∥ Σ (Fin n) (Bool→Type ∘ f) ∥₁ ≃ Bool→Type (trueForSome n f)
FinSum∃≃ n f =
  propBiimpl→Equiv isPropPropTrunc isPropBool→Type
    (Prop.rec isPropBool→Type (FinSum∃→ n f))
    (∣_∣₁ ∘ FinSum∃← n f)

FinSum∀≃ : (n : ℕ)(f : Fin n → Bool) → ((x : Fin n) → Bool→Type (f x)) ≃ Bool→Type (trueForAll n f)
FinSum∀≃ 0 _ = isContr→≃Unit (isContrΠ⊥)
FinSum∀≃ (suc n) f =
    Π⊎≃
  ⋆ Σ-cong-equiv (ΠUnit (Bool→Type ∘ f ∘ inl)) (λ _ → FinSum∀≃ n (f ∘ inr))
  ⋆ Bool→Type×≃ _ _

-- internal equality

FinSum≡ : (n : ℕ) → (a b : Fin n) → Bool
FinSum≡ 0 _ _ = true
FinSum≡ (suc n) (inl tt) (inl tt) = true
FinSum≡ (suc n) (inl tt) (inr y) = false
FinSum≡ (suc n) (inr x) (inl tt) = false
FinSum≡ (suc n) (inr x) (inr y) = FinSum≡ n x y

isSetFinSum : (n : ℕ)→ isSet (Fin n)
isSetFinSum 0 = isProp→isSet isProp⊥
isSetFinSum (suc n) = isSet⊎ (isProp→isSet isPropUnit) (isSetFinSum n)

FinSum≡≃ : (n : ℕ) → (a b : Fin n) → (a ≡ b) ≃ Bool→Type (FinSum≡ n a b)
FinSum≡≃ 0 _ _ = isContr→≃Unit (isProp→isContrPath isProp⊥ _ _)
FinSum≡≃ (suc n) (inl tt) (inl tt) = isContr→≃Unit (inhProp→isContr refl (isSetFinSum _ _ _))
FinSum≡≃ (suc n) (inl tt) (inr y) = invEquiv (⊎Path.Cover≃Path _ _) ⋆ uninhabEquiv (λ x → ⊥.rec* x) (λ x → ⊥.rec x)
FinSum≡≃ (suc n) (inr x) (inl tt) = invEquiv (⊎Path.Cover≃Path _ _) ⋆ uninhabEquiv (λ x → ⊥.rec* x) (λ x → ⊥.rec x)
FinSum≡≃ (suc n) (inr x) (inr y) = invEquiv (_ , isEmbedding-inr x y) ⋆ FinSum≡≃ n x y

-- propositional truncation of Fin

-- decidability of Fin

DecFin : (n : ℕ) → Dec (Fin n)
DecFin 0 = no (idfun _)
DecFin (suc n) = yes fzero

-- propositional truncation of Fin

Dec∥Fin∥ : (n : ℕ) → Dec ∥ Fin n ∥₁
Dec∥Fin∥ n = Dec∥∥ (DecFin n)

-- some properties about cardinality

fzero≠fone : {n : ℕ} → ¬ (fzero ≡ fsuc fzero)
fzero≠fone {n = n} = FinSum≡≃ (suc (suc n)) fzero (fsuc fzero) .fst

Fin>0→isInhab : (n : ℕ) → 0 < n → Fin n
Fin>0→isInhab 0 p = ⊥.rec (¬-<-zero p)
Fin>0→isInhab (suc n) p = fzero

Fin>1→hasNonEqualTerm : (n : ℕ) → 1 < n → Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] ¬ i ≡ j
Fin>1→hasNonEqualTerm 0 p = ⊥.rec (snotz (≤0→≡0 p))
Fin>1→hasNonEqualTerm 1 p = ⊥.rec (snotz (≤0→≡0 (pred-≤-pred p)))
Fin>1→hasNonEqualTerm (suc (suc n)) _ = fzero , fsuc fzero , fzero≠fone

isEmpty→Fin≡0 : (n : ℕ) → ¬ Fin n → 0 ≡ n
isEmpty→Fin≡0 0 _ = refl
isEmpty→Fin≡0 (suc n) p = ⊥.rec (p fzero)

isInhab→Fin>0 : (n : ℕ) → Fin n → 0 < n
isInhab→Fin>0 0 i = ⊥.rec i
isInhab→Fin>0 (suc n) _ = suc-≤-suc zero-≤

hasNonEqualTerm→Fin>1 : (n : ℕ) → (i j : Fin n) → ¬ i ≡ j → 1 < n
hasNonEqualTerm→Fin>1 0 i _ _ = ⊥.rec i
hasNonEqualTerm→Fin>1 1 i j p = ⊥.rec (p (isContr→isProp isContrFinSum1 i j))
hasNonEqualTerm→Fin>1 (suc (suc n)) _ _ _ = suc-≤-suc (suc-≤-suc zero-≤)

Fin≤1→isProp : (n : ℕ) → n ≤ 1 → isProp (Fin n)
Fin≤1→isProp 0 _ = isProp⊥
Fin≤1→isProp 1 _ = isContr→isProp isContrFinSum1
Fin≤1→isProp (suc (suc n)) p = ⊥.rec (¬-<-zero (pred-≤-pred p))

isProp→Fin≤1 : (n : ℕ) → isProp (Fin n) → n ≤ 1
isProp→Fin≤1 0 _ = ≤-solver 0 1
isProp→Fin≤1 1 _ = ≤-solver 1 1
isProp→Fin≤1 (suc (suc n)) p = ⊥.rec (fzero≠fone (p fzero (fsuc fzero)))

-- automorphisms of FinSum

@0 FinSum≃≃ : (n : ℕ) → (Fin n ≃ Fin n) ≃ Fin (LehmerCode.factorial n)
FinSum≃≃ _ =
    equivComp (FinSum≃Fin _) (FinSum≃Fin _)
  ⋆ LehmerCode.lehmerEquiv
  ⋆ LehmerCode.lehmerFinEquiv
  ⋆ invEquiv (FinSum≃Fin _)
