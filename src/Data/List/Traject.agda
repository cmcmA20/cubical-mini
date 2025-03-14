{-# OPTIONS --safe #-}
module Data.List.Traject where

open import Prelude
open import Meta.Effect

open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.Prefix
open import Data.List.Operations.Properties

open import Data.Empty hiding (_≠_)
open import Data.Reflects as Reflects
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe

-- function trajectory

traj : {ℓ : Level} {A : 𝒰 ℓ}
     → (A → A) → A → ℕ → List A
traj f x  zero   = []
traj f x (suc n) = x ∷ traj f (f x) n

traj-snoc : {ℓ : Level} {A : 𝒰 ℓ}
          → {f : A → A} {x : A} {n : ℕ}
          → traj f x (suc n) ＝ traj f x n ∷r iter n f x
traj-snoc         {n = zero}  = refl
traj-snoc {f} {x} {n = suc n} =
  ap (x ∷_) (  traj-snoc {f = f} {x = f x} {n = n}
             ∙ ap (λ q → snoc (traj f (f x) n) q) (iter-swap n 1 f x) )

traj-map : {ℓ : Level} {A : 𝒰 ℓ}
         → {f : A → A} {x : A} {n : ℕ}
         → map f (traj f x n) ＝ traj f (f x) n
traj-map         {n = zero}  = refl
traj-map {f} {x} {n = suc n} = ap (f x ∷_) traj-map

traj-last : {ℓ : Level} {A : 𝒰 ℓ}
          → {f : A → A} {x : A} {n : ℕ}
          → last x (traj f (f x) n) ＝ iter n f x
traj-last         {n = zero}  = refl
traj-last {f} {x} {n = suc n} =  
    ap (last x) (traj-snoc {f = f} {x = f x} {n = n})
  ∙ (last-snoc {xs = traj f (f x) n})
  ∙ iter-swap n 1 f x

traj-length : {ℓ : Level} {A : 𝒰 ℓ}
            → {f : A → A} {x : A} {n : ℕ}
            → length (traj f x n) ＝ n
traj-length {n = zero}  = refl
traj-length {n = suc n} = ap suc traj-length

-- TODO unneeded?
traj-!ᵐ : {ℓ : Level} {A : 𝒰 ℓ}
        → {f : A → A} {x : A} {n k : ℕ} 
        → k < n → traj f x n !ᵐ k ＝ just (iter k f x)
traj-!ᵐ         {n = zero}              k<n = false! k<n
traj-!ᵐ         {n = suc n} {k = zero}  k<n = refl
traj-!ᵐ {f} {x} {n = suc n} {k = suc k} k<n =
  traj-!ᵐ {f = f} {x = f x} (<-peel k<n) ∙ ap just (iter-swap k 1 f x)

∈-traj : {ℓ : Level} {A : 𝒰 ℓ}
        → {f : A → A} {x : A} {k n : ℕ}
        → k < n
        → iter k f x ∈ traj f x n
∈-traj         {k = k}     {n = zero}  k<n = false! k<n
∈-traj         {k = zero}  {n = suc n} k<n = here refl
∈-traj {f} {x} {k = suc k} {n = suc n} k<n =
  there $ subst (_∈ traj f (f x) n) (iter-swap k 1 f x) $
  ∈-traj {f = f} {x = f x} (<-peel k<n)

traj-∈ : {ℓ : Level} {A : 𝒰 ℓ}
        → {f : A → A} {x : A} {n : ℕ} {z : A}
        → z ∈ traj f x n
        → Σ[ k ꞉ ℕ ] (k < n) × (z ＝ iter k f x)
traj-∈         {n = zero}             = false!
traj-∈         {n = suc n} (here e)   = 0 , z<s , e
traj-∈ {f} {x} {n = suc n} (there zm) =
  let (k , k< , e) = traj-∈ {n = n} zm in
  suc k , s<s k< , e ∙ iter-swap k 1 f x

traj-add : {ℓ : Level} {A : 𝒰 ℓ}
         → {f : A → A} {x : A} {m n : ℕ} 
         → traj f x (m + n) ＝ traj f x m ++ traj f (iter m f x) n
traj-add         {m = zero}      = refl
traj-add {f} {x} {m = suc m} {n} =
  ap (x ∷_) (  traj-add {x = f x} {m = m}
             ∙ ap (λ q → traj f (f x) m ++ traj f q n) (iter-swap m 1 f x))

traj-prefix : {ℓ : Level} {A : 𝒰 ℓ}
            → {f : A → A} {x : A} {m n : ℕ}
            → m ≤ n
            → Prefix (traj f x m) (traj f x n)
traj-prefix {m = zero}              m≤n = []-prefix
traj-prefix {m = suc m} {n = zero}  m≤n = false! m≤n
traj-prefix {m = suc m} {n = suc n} m≤n = ∷-prefix refl (traj-prefix (≤-peel m≤n))

traj-take : {ℓ : Level} {A : 𝒰 ℓ}
          → {f : A → A} {x : A} {n k : ℕ} 
          → k ≤ n
          → take k (traj f x n) ＝ traj f x k
traj-take                 {k = zero}  k≤n = refl
traj-take     {n = zero}  {k = suc k} k≤n = false! k≤n
traj-take {x} {n = suc n} {k = suc k} k≤n = ap (x ∷_) (traj-take (≤-peel k≤n))

-- unique trajectory

traj-uniq→¬loop : {ℓ : Level} {A : 𝒰 ℓ}
                → {f : A → A} {x : A} {n : ℕ}
                → Uniq (traj f x n)
                → ∀ m → suc m < n → f (iter m f x) ≠ x
traj-uniq→¬loop         {n = zero}          u m m<n e = false! m<n
traj-uniq→¬loop {f} {x} {n = suc n} (x∉ ∷ᵘ _) m m<n e =
  x∉ (subst (_∈ traj f (f x) n) (iter-swap m 1 f x ∙ e) (∈-traj (<-peel m<n)))

traj-uniq→iter-inj : {ℓ : Level} {A : 𝒰 ℓ}
                   → {f : A → A} {x : A} {n : ℕ}
                   → Uniq (traj f x n)
                   → ∀ p q → p < n → q < n → iter p f x ＝ iter q f x → p ＝ q
traj-uniq→iter-inj                             u   zero    zero   p<n q<n e = refl
traj-uniq→iter-inj                             u   zero   (suc q) p<n q<n e =
  absurd (traj-uniq→¬loop u q q<n (e ⁻¹))
traj-uniq→iter-inj                             u  (suc p)  zero   p<n q<n e =
  absurd (traj-uniq→¬loop u p p<n e)
traj-uniq→iter-inj         {n = zero}          u  (suc p) (suc q) p<n q<n e = false! p<n
traj-uniq→iter-inj {f} {x} {n = suc n} (_ ∷ᵘ u) (suc p) (suc q) p<n q<n e =
  ap suc $
  traj-uniq→iter-inj {n = n} u p q (<-peel p<n) (<-peel q<n) $
  iter-swap p 1 f x ∙ e ∙ iter-swap q 1 f x ⁻¹

traj-iter-inj→uniq : {ℓ : Level} {A : 𝒰 ℓ}
                   → {f : A → A} {x : A} {n : ℕ}
                   → (∀ p q → p < n → q < n → iter p f x ＝ iter q f x → p ＝ q)
                   → Uniq (traj f x n)
traj-iter-inj→uniq         {n = zero}  inj = []ᵘ
traj-iter-inj→uniq {f} {x} {n = suc n} inj =
  (λ x∈ →
       let (k , k< , e) = traj-∈ x∈ in
       false! $ inj 0 (suc k) z<s (s<s k<) (e ∙ iter-swap k 1 f x))
  ∷ᵘ
  traj-iter-inj→uniq λ p q p<n q<n e →
                        suc-inj (inj (suc p) (suc q) (s<s p<n) (s<s q<n) $
                        iter-swap 1 p f x ∙ e ∙ iter-swap 1 q f x ⁻¹)

uniq-under-∉ : {ℓ : Level} {A : 𝒰 ℓ}
              → {f : A → A} {x : A} {m n : ℕ}
              → Uniq (traj f x n)
              → ∀ k → m ≤ k → k < n → iter k f x ∉ traj f x m
uniq-under-∉ ut k m≤k k<n ik∈ =
  let (l , l< , ize) = traj-∈ ik∈
      l<k = <-≤-trans l< m≤k
   in
  <→≠ l<k (traj-uniq→iter-inj ut k l k<n (<-trans l<k k<n) ize ⁻¹)
