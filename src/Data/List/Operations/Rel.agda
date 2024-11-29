{-# OPTIONS --safe #-}
module Data.List.Operations.Rel where

open import Meta.Prelude
open import Foundations.Base

open import Data.Empty as Empty
open import Data.Bool.Base as Bool
open import Data.Bool.Path
open import Data.Sum.Base as Sum
open import Data.Reflects.Base
open import Data.Dec.Base

open import Data.List.Base as List
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.At
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.Perm
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Properties

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  cmp : A → A → Bool
  _≤_ _<_ : A → A → 𝒰 ℓ′
  x y z w : A
  xs : List A

insert-perm : Perm (insert cmp x xs) (x ∷ xs)
insert-perm           {xs = []}     = perm-refl
insert-perm {cmp} {x} {xs = y ∷ xs} with cmp x y
... | false = ptrans (pprep refl insert-perm) (pswap refl refl perm-refl)
... | true  = perm-refl

insertion-sort-perm : Perm (insertion-sort cmp xs) xs
insertion-sort-perm {xs = []}     = perm-refl
insertion-sort-perm {xs = x ∷ xs} = ptrans insert-perm (pprep refl insertion-sort-perm)

insert-sorted : {R : ∀ x y → Reflects (x ≤ y) (cmp x y)}
              → Trans _≤_ → (∀ x y → ¬ x ≤ y → y ≤ x)
              → ∀ {xs} → Sorted _≤_ xs → Sorted _≤_ (insert cmp x xs)
insert-sorted               _  _   {xs = []}     []ˢ    = ∷ˢ []ʳ
insert-sorted {cmp} {x} {R} tr tot {xs = y ∷ xs} (∷ˢ r) with cmp x y | recall (cmp x) y
... | false | ⟪ eq ⟫ = ∷ˢ (sorted-at0→related
                              (insert-sorted {R = R} tr tot (related→sorted r))
                              (all→atweak (perm-all (perm-sym insert-perm)
                                                    (tot x y (so→false! ⦃ R x y ⦄ $ not-so $ ¬so≃is-false ⁻¹ $ eq)
                                                              ∷ (related→all ⦃ tr ⦄ r)))
                                          0))
... | true  | ⟪ eq ⟫ = ∷ˢ ((so→true! ⦃ R x y ⦄ $ so≃is-true ⁻¹ $ eq) ∷ʳ r)

insertion-sort-sorted : {R : ∀ x y → Reflects (x ≤ y) (cmp x y)}
                      → Trans _≤_ → (∀ x y → ¬ x ≤ y → y ≤ x)
                      → ∀ {xs} → Sorted _≤_ (insertion-sort cmp xs)
insertion-sort-sorted _  _   {xs = []}     = []ˢ
insertion-sort-sorted {R} tr tot {xs = x ∷ xs} =
  insert-sorted {R = R} tr tot
    (insertion-sort-sorted {R = R} tr tot {xs})

-- sorting with strict comparison

insert-sorted-uniq-strict : {R : ∀ x y → Reflects (x < y) (cmp x y)}
                          → Trans _<_ → (∀ x y → ¬ x < y → (y < x) ⊎ (x ＝ y))
                          → ∀ {xs} → x ∉ xs → Uniq xs
                          → Sorted _<_ xs → Sorted _<_ (insert cmp x xs)
insert-sorted-uniq-strict               _  _    {xs = []}     _   _         []ˢ   = ∷ˢ []ʳ
insert-sorted-uniq-strict {cmp} {x} {R} tr stot {xs = y ∷ xs} nx (ny ∷ᵘ u) (∷ˢ r) with cmp x y | recall (cmp x) y
... | false | ⟪ eq ⟫ =
  let (ne , nxs) = ¬Any-uncons nx in
  ∷ˢ (sorted-at0→related
        (insert-sorted-uniq-strict {R = R} tr stot nxs u (related→sorted r))
        (all→atweak (perm-all (perm-sym insert-perm)
                              ([ id , (λ e → absurd (ne e)) ]ᵤ (stot x y (so→false! ⦃ R x y ⦄ $ not-so $ ¬so≃is-false ⁻¹ $ eq))
                               ∷ (related→all ⦃ tr ⦄ r)))
                    0))
... | true  | ⟪ eq ⟫ = ∷ˢ ((so→true! ⦃ R x y ⦄ $ so≃is-true ⁻¹ $ eq) ∷ʳ r)

insertion-sort-sorted-uniq-strict : {R : ∀ x y → Reflects (x < y) (cmp x y)}
                                  → Trans _<_ → (∀ x y → ¬ x < y → (y < x) ⊎ (x ＝ y))
                                  → ∀ {xs} → Uniq xs
                                  → Sorted _<_ (insertion-sort cmp xs)
insertion-sort-sorted-uniq-strict           _  _    {xs = []}     []ᵘ       = []ˢ
insertion-sort-sorted-uniq-strict {cmp} {R} tr stot {xs = x ∷ xs} (nx ∷ᵘ u) =
  let p = insertion-sort-perm {xs = xs} in
  insert-sorted-uniq-strict {R = R} tr stot
    (contra (≈↔→≈ {S = insertion-sort cmp xs} {T = xs} (perm→bag-equiv p) .fst) nx)
    (perm-unique (perm-sym p) u)
    (insertion-sort-sorted-uniq-strict {R = R} tr stot u)

-- nub

nub-acc-ope : ∀ {acc xs}
            → OPE (nub-acc cmp acc xs) xs
nub-acc-ope             {xs = []}     = odone
nub-acc-ope {cmp} {acc} {xs = x ∷ xs} with any (cmp x) acc
... | false = otake refl nub-acc-ope
... | true  = odrop nub-acc-ope

nub-ope : ∀ {xs}
        → OPE (nub cmp xs) xs
nub-ope = nub-acc-ope {acc = []}

⊆-nub-acc : {R : ∀ x y → Reflects (x ＝ y) (cmp x y)}
           → ∀ {acc xs}
           → xs ⊆ (acc ++ nub-acc cmp acc xs)
⊆-nub-acc                 {xs = []}          hx        = false! hx
⊆-nub-acc {cmp} {R} {acc} {xs = y ∷ xs} {x} (here e)   with any (cmp y) acc | recall (any (cmp y)) acc
... | false | _      = any-++-r (here e)
... | true  | ⟪ eq ⟫ =
  any-++-l $
  subst (_∈ acc) (e ⁻¹) $
  so→true! ⦃ Reflects-any {xs = acc} (R y) ⦄ $ so≃is-true ⁻¹ $ eq
⊆-nub-acc {cmp} {R} {acc} {xs = y ∷ xs} {x} (there hx) with any (cmp y) acc
... | false =
  (any-uncons $ ⊆-nub-acc {cmp = cmp} {R} {acc = y ∷ acc} hx) &
  [ (λ e → any-++-r (here e)) , [ any-++-l {xs = acc} , any-++-r ∘ there ]ᵤ ∘ any-split ]ᵤ
... | true  = ⊆-nub-acc {R = R} {acc = acc} hx

⊆-nub : {R : ∀ x y → Reflects (x ＝ y) (cmp x y)}
       → ∀ {xs}
       → xs ⊆ nub cmp xs
⊆-nub {R} = ⊆-nub-acc {R = R}

nub-≈ : {R : ∀ x y → Reflects (x ＝ y) (cmp x y)}
      → ∀ {xs}
      → nub cmp xs ≈ xs
nub-≈ {R} = (ope→subset nub-ope) , ⊆-nub {R = R}

nub-acc-unique : {R : ∀ x y → Reflects (x ＝ y) (cmp x y)}
               → ∀ {acc xs}
               → let res = nub-acc cmp acc xs in
                 Uniq res × All (_∉ acc) res
nub-acc-unique                 {xs = []}     = []ᵘ , []
nub-acc-unique {cmp} {R} {acc} {xs = x ∷ xs} with any (cmp x) acc | recall (any (cmp x)) acc
... | false | ⟪ eq ⟫ =
  let (u , a) = nub-acc-unique {R = R} {acc = x ∷ acc} {xs = xs}
      nx = so→false! {Q = ⊥} ⦃ Reflects-any {xs = acc} (R x) ⦄ $ not-so $ ¬so≃is-false ⁻¹ $ eq
    in
  ((λ hx → All→∀∈ a x hx (here refl)) ∷ᵘ u) , (nx ∷ all-map (λ {x = z} nz hz → nz (there hz)) a)
... | true  | _  = nub-acc-unique {R = R} {acc = acc} {xs = xs}

nub-unique : {R : ∀ x y → Reflects (x ＝ y) (cmp x y)}
           → ∀ {xs} → Uniq (nub cmp xs)
nub-unique {R} {xs} = nub-acc-unique {R = R} {acc = []} {xs = xs} .fst
