{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Operations.Discrete where

open import Meta.Prelude
open import Logic.Discreteness

open import Data.Empty.Base
open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Bool.Properties
open import Data.Maybe.Base
open import Data.Sum.Base
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Nat.Two
open import Data.Nat.Order.Base
open import Data.Dec.Base
open import Data.Reflects.Base as Reflects

open import Data.List.Base as List
open import Data.List.Operations
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Has
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Correspondences.Binary.Perm

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  x : A
  xs : List A

has : ⦃ d : is-discrete A ⦄ → A → List A → Bool
has a = any (λ x → ⌊ x ≟ a ⌋)

elem= : ⦃ A-dis : is-discrete A ⦄
      → A → List A → Bool
elem= = elem (λ a b → ⌊ a ≟ b ⌋)

subseq : ⦃ A-dis : is-discrete A ⦄
        → List A → List A → Bool
subseq     []       ys       = true
subseq     (x ∷ xs) []       = false
subseq xs₀@(x ∷ xs) (y ∷ ys) = subseq (if ⌊ x ≟ y ⌋ then xs else xs₀) ys

related? : {R : A → A → 𝒰 ℓ′}
         → Decidable R
         → A → List A → Bool
related?     R? x0 []       = true
related? {R} R? x0 (x ∷ xs) =
  ⌊ R? {x = x0} {x = x} ⌋ and related? {R = R} R? x xs

sorted? : {R : A → A → 𝒰 ℓ′}
        → Decidable R
        → List A → Bool
sorted?     R? []       = true
sorted? {R} R? (x ∷ xs) = related? {R = R} R? x xs

perm? : ⦃ d : is-discrete A ⦄ → List A → List A → Bool
perm? xs ys = all (λ q → count (λ x → ⌊ x ≟ q ⌋) xs == count (λ y → ⌊ y ≟ q ⌋) ys) (xs ++ ys)

-- properties

Reflects-has : ⦃ d : is-discrete A ⦄ {x : A} {xs : List A}
             → Reflects (Has x xs) (has x xs)
Reflects-has {x} {xs} = Reflects-any-dec {xs = xs} (λ y → y ≟ x)

Reflects-subseq : ⦃ d : is-discrete A ⦄ {xs ys : List A}
                → Reflects (OPE xs ys) (subseq xs ys)
Reflects-subseq {xs = []}     {ys}          = ofʸ ope-init
Reflects-subseq {xs = x ∷ xs} {ys = []}     = ofⁿ ¬ope-cons-nil
Reflects-subseq {xs = x ∷ xs} {ys = y ∷ ys} =
  caseᵈ x ＝ y
    return (λ q → Reflects (OPE (x ∷ xs) (y ∷ ys)) (subseq (if ⌊ q ⌋ then xs else x ∷ xs) ys))
    of λ where
           (yes x=y) →
              Reflects.dmap (otake x=y)
                            (contra ope-uncons)
                            (Reflects-subseq {xs = xs} {ys = ys})
           (no x≠y) →
              Reflects.dmap odrop
                            (contra λ where
                                       (otake x=y o) → absurd (x≠y x=y)
                                       (odrop o) → o)
                            (Reflects-subseq {xs = x ∷ xs} {ys = ys})

Reflects-related : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
                 → (R? : ∀ {x y} → Dec (R x y)) {- `Decidable R` fails -}
                 → ∀ {x0} {xs} → Reflects (Related R x0 xs) (related? {R = R} R? x0 xs)
Reflects-related     R? {x0} {xs = []}     = ofʸ []ʳ
Reflects-related {R} R? {x0} {xs = x ∷ xs} =
  Reflects.dmap
    (λ where (r , rs) → r ∷ʳ rs) (contra (λ where (r ∷ʳ rs) → r , rs))
    (Reflects-× ⦃ rp = reflects-does (R? {x = x0} {y = x}) ⦄ ⦃ rq = Reflects-related {R = R} R? {x0 = x} {xs = xs} ⦄)

Reflects-sorted : {A : 𝒰 ℓ} {R : A → A → 𝒰 ℓ′}
                → (R? : ∀ {x y} → Dec (R x y)) {- `Decidable R` fails -}
                → ∀ {xs} → Reflects (Sorted R xs) (sorted? {R = R} R? xs)
Reflects-sorted     R? {xs = []}     = ofʸ []ˢ
Reflects-sorted {R} R? {xs = x ∷ xs} =
  Reflects.dmap ∷ˢ (contra (λ where (∷ˢ r) → r))
    (Reflects-related {R = R} R? {x0 = x} {xs})


Reflects-perm-count : ⦃ d : is-discrete A ⦄ {xs ys : List A}
                    → Reflects (∀ p → count p xs ＝ count p ys) (perm? xs ys)
Reflects-perm-count {A} {xs} {ys} =
  Reflects.dmap
    (λ a p → aux a p (suc (count p (xs ++ ys))) <-ascend)
    (contra λ e → all-trivial λ a → true→so! ⦃ Reflects-ℕ-Path {m = count (λ x → ⌊ x ≟ a ⌋) xs} ⦄ (e λ z → ⌊ z ≟ a ⌋))
    (Reflects-all-bool {xs = xs ++ ys})
  where
  cnteq : (p : A → Bool) (zs : List A) (a : A) → So (p a)
        → count p zs ＝ count (λ z → ⌊ z ≟ a ⌋) zs + count (λ z → not ⌊ z ≟ a ⌋ and p z) zs
  cnteq p zs a pa =   +-zero-r (count p zs) ⁻¹
                    ∙ ap² _+_ (ap (λ q → count q zs) (fun-ext λ x → caseᵈ x ＝ a
                                                                      return (λ q → p x ＝ ⌊ q ⌋ or not ⌊ q ⌋ and p x)
                                                                      of λ where
                                                                             (yes eq) → ap p eq ∙ (so≃is-true $ pa)
                                                                             (no neq) → refl))
                              (count-false zs ⁻¹ ∙ ap (λ q → count q zs) (fun-ext λ x →   ap (_and p x) (and-compl ⌊ x ≟ a ⌋ ⁻¹)
                                                                                        ∙ and-assoc ⌊ x ≟ a ⌋ (not ⌊ x ≟ a ⌋) (p x)))
                    ∙ count-union-inter (λ z → ⌊ z ≟ a ⌋) (λ z → not ⌊ z ≟ a ⌋ and p z) zs

  aux : All (λ q → So (count (λ x → ⌊ x ≟ q ⌋) xs == count (λ y → ⌊ y ≟ q ⌋) ys)) (xs ++ ys)
      → (p : A → Bool)
      → ∀ n → count p (xs ++ ys) < n
      → count p xs ＝ count p ys
  aux axy p  zero   lt = false! lt
  aux axy p (suc n) lt =
    [ (λ 0<c → let anyp = so→true! ⦃ Reflects-any-bool {xs = xs ++ ys} ⦄ $
                          true→so! ⦃ Reflects-0<count p (xs ++ ys) ⦄ 0<c
                   (a , ha , pa) = Any→ΣHas anyp
                   ceq = so→true! ⦃ Reflects-ℕ-Path {m = count (λ x → ⌊ x ≟ a ⌋) xs} ⦄ (All→∀Has axy a ha)
                 in   cnteq p xs a pa
                    ∙ ap² _+_ ceq (aux axy (λ z → not ⌊ z ≟ a ⌋ and p z) n
                         (<-≤-trans (<-≤-trans
                                       (<-+-0lr (so→true! ⦃ Reflects-0<count (λ x → ⌊ x ≟ a ⌋) (xs ++ ys) ⦄ $
                                                 true→so! ⦃ Reflects-any-dec {xs = xs ++ ys} (λ x → x ≟ a) ⦄ ha))
                                       (=→≤ (cnteq p (xs ++ ys) a pa ⁻¹)))
                                    (≤≃<suc ⁻¹ $ lt)))
                    ∙ cnteq p ys a pa ⁻¹ )
    , (λ c=0 → let (ex , ey) = +=0-2 (count p xs) (count p ys) ((c=0 ∙ count-++ p xs ys) ⁻¹) in
               ex ∙ ey ⁻¹)
    ]ᵤ (≤≃<⊎= {n = count p (xs ++ ys)} $ z≤)

Reflects-perm : ⦃ d : is-discrete A ⦄ {xs ys : List A}
              → Reflects (Perm xs ys) (perm? xs ys)
Reflects-perm {A} {xs} =
  Reflects.dmap to (contra fro) (Reflects-perm-count {xs = xs})
  where
  to : {as bs : List A}
     → ((p : A → Bool) → count p as ＝ count p bs) → Perm as bs
  to {as} {bs = []}     ceq =
    let asnil = length=0→nil $ count-true as ⁻¹ ∙ ceq (λ _ → true) ∙ count-true (the (List A) []) in
    subst (λ q → Perm q []) (asnil ⁻¹) perm-refl
  to {as} {bs = b ∷ bs} ceq =
    let hasb = so→true! ⦃ Reflects-any-dec {xs = as} (λ x → x ≟ b) ⦄ $
               true→so! ⦃ Reflects-0<count (λ x → ⌊ x ≟ b ⌋) as ⦄ $
               subst (0 <_) (ceq (λ x → ⌊ x ≟ b ⌋) ⁻¹)
                     (given-yes (the (b ＝ b) refl)
                        return (λ q → 0 < bit ⌊ q ⌋ + count (λ x → ⌊ x ≟ b ⌋) bs)
                        then z<s)
        (ls , rs , eas) = Has-split hasb
        ih = to {as = ls ++ rs} {bs = bs} λ p →
                 count-++ p ls rs
               ∙ +-inj-l (bit (p b)) (count p ls + count p rs) (count p bs)
                 (  +-comm-assoc (bit (p b)) (count p ls) (count p rs)
                  ∙ count-++ p ls (b ∷ rs) ⁻¹
                  ∙ ap (count p) eas ⁻¹
                  ∙ ceq p)
      in
    ptrans
      (subst (λ q → Perm q (b ∷ ls ++ rs)) (eas ⁻¹)
             (perm-sym perm-cons-cat-commassoc))
      (pprep refl ih)

  fro : {as bs : List A}
      → Perm as bs → (p : A → Bool) → count p as ＝ count p bs
  fro (peq e)                                                  p = ap (count p) e
  fro (pprep e pe)                                             p = ap² _+_ (ap (λ q → bit (p q)) e) (fro pe p)
  fro (pswap {xs = xs′} {ys = ys′} {x} {y} {x′} {y′} ex ey pe) p =
      +-assoc (bit (p x)) (bit (p y)) (count p xs′)
    ∙ ap² _+_ (  ap² _+_ (ap (bit ∘ p) ex) (ap (bit ∘ p) ey)
               ∙ +-comm (bit (p x′)) (bit (p y′)))
              (fro pe p)
    ∙ +-assoc (bit (p y′)) (bit (p x′)) (count p ys′) ⁻¹
  fro (ptrans pe₁ pe₂)                                         p = fro pe₁ p ∙ fro pe₂ p
