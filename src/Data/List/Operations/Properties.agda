{-# OPTIONS --safe #-}
module Data.List.Operations.Properties where

open import Foundations.Base

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Empty as Empty
open import Data.Bool.Base as Bool
open import Data.Bool.Properties
open import Data.Sum.Base as Sum
open import Data.Dec.Base as Dec
open import Data.Reflects.Base as Reflects
open import Data.List.Base as List
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Order.Base
open import Data.Nat.Properties

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

-- length

length=0→nil : {xs : List A} → length xs ＝ 0 → xs ＝ []
length=0→nil {xs = []}     eq = refl
length=0→nil {xs = x ∷ xs} eq = absurd (suc≠zero eq)

length=1→sng : {A : 𝒰 ℓ} {xs : List A}
             → length xs ＝ 1 → Σ[ x ꞉ A ] (xs ＝ x ∷ [])
length=1→sng {xs = []}     eq = absurd (zero≠suc eq)
length=1→sng {xs = x ∷ xs} eq = x , ap (x ∷_) (length=0→nil (suc-inj eq))

++-length : (xs ys : List A) → length (xs ++ ys) ＝ length xs + length ys
++-length []       ys = refl
++-length (x ∷ xs) ys = ap suc (++-length xs ys)

++-same-inj : (as xs : List A) {bs ys : List A}
            → length as ＝ length xs
            → as ++ bs ＝ xs ++ ys
            → (as ＝ xs) × (bs ＝ ys)
++-same-inj     []       []       el e = refl , e
++-same-inj     []       (x ∷ xs) el e = absurd (zero≠suc el)
++-same-inj     (a ∷ as) []       el e = absurd (suc≠zero el)
++-same-inj {A} (a ∷ as) (x ∷ xs) el e =
  let ih = ++-same-inj as xs (suc-inj el) (∷-tail-inj e) in
  ap² {C = λ _ _ → List A} _∷_ (∷-head-inj e) (ih .fst) , ih .snd

-- snoc

snoc-append : (xs : List A) {x : A} → snoc xs x ＝ xs ++ x ∷ []
snoc-append []       = refl
snoc-append (y ∷ xs) = ap (y ∷_) (snoc-append xs)

++-snoc : (xs ys : List A) (y : A) → snoc xs y ++ ys ＝ xs ++ y ∷ ys
++-snoc []       ys y = refl
++-snoc (x ∷ xs) ys y = ap (x ∷_) (++-snoc xs ys y)

snoc-++ : (xs ys : List A) (y : A) → snoc (xs ++ ys) y ＝ xs ++ snoc ys y
snoc-++ []       ys y = refl
snoc-++ (x ∷ xs) ys y = ap (x ∷_) (snoc-++ xs ys y)

snoc-elim : (P : List A → 𝒰 ℓ′)
  → P []
  → (∀ xs x → P xs → P (snoc xs x))
  → ∀ xs → P xs
snoc-elim P p[] ps xs = go [] xs p[]
  where
  go : ∀ xs ys → P xs → P (xs ++ ys)
  go xs []       pxs = subst P (sym $ ++-id-r xs) pxs
  go xs (y ∷ ys) pxs = subst P (++-snoc xs ys y) (go (snoc xs y) ys (ps xs y pxs))

snoc-length : (xs : List A) {x : A} → length (snoc xs x) ＝ suc (length xs)
snoc-length xs {x} = ap length (snoc-append xs) ∙ ++-length xs (x ∷ []) ∙ +-comm (length xs) 1

snoc-inj : {xs ys : List A} {z w : A} → snoc xs z ＝ snoc ys w → (xs ＝ ys) × (z ＝ w)
snoc-inj     {xs = []}     {ys = []}     e = refl , (∷-head-inj e)
snoc-inj     {xs = []}     {ys = y ∷ ys} e = absurd (zero≠suc (suc-inj (ap length e ∙ ap suc (snoc-length ys))))
snoc-inj     {xs = x ∷ xs} {ys = []}     e = absurd (suc≠zero (suc-inj (ap suc (snoc-length xs ⁻¹) ∙ ap length e)))
snoc-inj {A} {xs = x ∷ xs} {ys = y ∷ ys} e = let ih = snoc-inj (∷-tail-inj e) in
                                             ap² {C = λ _ _ → List A} _∷_ (∷-head-inj e) (ih .fst) , ih .snd

-- all

reflects-all : ∀ (p : A → Bool) xs
             → Reflects (All (So ∘ p) xs) (all p xs)
reflects-all p []       = ofʸ []
reflects-all p (x ∷ xs) with p x | recall p x
... | false | ⟪ e ⟫ = ofⁿ (λ where (a ∷ as) → ¬-so-false (subst So e a))
... | true  | ⟪ e ⟫ = Reflects.dmap (λ a → subst So (e ⁻¹) oh ∷ a)
                       (λ ne → λ where (px ∷ a) → ne a)
                       (reflects-all p xs)

all?-++ : ∀ {p : A → Bool} {xs ys : List A}
        → all p (xs ++ ys) ＝ all p xs and all p ys
all?-++ {p} {xs = []}     {ys} = refl
all?-++ {p} {xs = x ∷ xs} {ys} = ap (p x and_) (all?-++ {xs = xs}) ∙ and-assoc (p x) (all p xs) (all p ys) ⁻¹

-- elem

elem= : ⦃ A-dis : is-discrete A ⦄
      → A → List A → Bool
elem= = elem (λ a b → ⌊ a ≟ b ⌋)

all-elem : ⦃ A-dis : is-discrete A ⦄
         → ∀ (P : A → 𝒰 ℓ′) xs
         → All P xs
         → (z : A) → ⌞ elem= z xs ⌟ → P z
all-elem P (x ∷ xs) (px ∷ a) z el with so→true! ⦃ reflects-or {x = ⌊ z ≟ x ⌋} ⦄ el
... | inl z=x = subst P (sym $ so→true! z=x) px
... | inr els = all-elem P xs a z els

elem-all : ⦃ di : is-discrete A ⦄
         → ∀ (P : A → 𝒰 ℓ′) xs
         → ((z : A) → ⌞ elem= z xs ⌟ → P z)
         → All P xs
elem-all        P []       f = []
elem-all {A} ⦃ di ⦄ P (x ∷ xs) f
  = f x (true→so! ⦃ reflects-or ⦄ (inl (true→so! {P = x ＝ x} refl)))
  ∷ elem-all P xs λ z el → f z (true→so! ⦃ reflects-or ⦄ (inr el))

reflects-all-dis : ⦃ A-dis : is-discrete A ⦄
                 → ∀ (p : A → Bool) xs
                 → Reflects (∀ x → ⌞ elem= x xs ⌟ → ⌞ p x ⌟) (all p xs)
reflects-all-dis p xs =
  Reflects.dmap
    (all-elem (So ∘ p) xs)
    (λ na e → na (elem-all (So ∘ p) xs e))
    (reflects-all p xs)


-- replicate

replicate-+ : {n m : ℕ} {z : A}
            → replicate (n + m) z ＝ replicate n z ++ replicate m z
replicate-+ {n = zero}      = refl
replicate-+ {n = suc n} {z} = ap (z ∷_) (replicate-+ {n = n})

replicate-snoc : {n : ℕ} {z : A}
               → replicate (suc n) z ＝ snoc (replicate n z) z
replicate-snoc {n} {z} = ap (λ q → replicate q z) (+-comm 1 n) ∙ replicate-+ {m = 1} ∙ snoc-append _ ⁻¹

All-replicate : {z : A} (xs : List A)
              → All (_＝ z) xs
              → xs ＝ replicate (length xs) z
All-replicate     []       []       = refl
All-replicate {z} (x ∷ xs) (xa ∷ a) = ap² List._∷_ xa (All-replicate xs a)


-- take & drop

take-nil : {n : ℕ}
         → take n (the (List A) []) ＝ []
take-nil {n = zero}  = refl
take-nil {n = suc _} = refl

drop-nil : {n : ℕ}
         → drop n (the (List A) []) ＝ []
drop-nil {n = zero}  = refl
drop-nil {n = suc _} = refl

length-take : {n : ℕ} {xs : List A}
            → length (take n xs) ＝ min n (length xs)
length-take {n = zero}                = refl
length-take {n = suc n} {xs = []}     = refl
length-take {n = suc n} {xs = x ∷ xs} = ap suc length-take

length-drop : {n : ℕ} {xs : List A}
            → length (drop n xs) ＝ length xs ∸ n
length-drop {n = zero}                = refl
length-drop {n = suc n} {xs = []}     = refl
length-drop {n = suc n} {xs = x ∷ xs} = length-drop {n = n}

take-+ : {n m : ℕ} {xs : List A}
       → take (n + m) xs ＝ take n xs ++ take m (drop n xs)
take-+ {n = zero}                = refl
take-+ {n = suc n} {xs = []}     = take-nil ⁻¹
take-+ {n = suc n} {xs = x ∷ xs} = ap (x ∷_) (take-+ {n = n})

drop-+ : {n m : ℕ} {xs : List A}
       → drop (n + m) xs ＝ drop m (drop n xs)
drop-+ {n = zero}                    = refl
drop-+ {n = suc n} {m} {xs = []}     = drop-nil {n = m} ⁻¹
drop-+ {n = suc n}     {xs = x ∷ xs} = drop-+ {n = n}

take-oversize : {n : ℕ} {xs : List A}
              → length xs ≤ n
              → take n xs ＝ xs
take-oversize {n = zero}                le = length=0→nil (≤0→=0 le) ⁻¹
take-oversize {n = suc n} {xs = []}     le = refl
take-oversize {n = suc n} {xs = x ∷ xs} le = ap (x ∷_) (take-oversize (≤-peel le))

drop-oversize : {n : ℕ} {xs : List A}
              → length xs ≤ n
              → drop n xs ＝ []
drop-oversize {n = zero}                le = length=0→nil (≤0→=0 le)
drop-oversize {n = suc n} {xs = []}     le = refl
drop-oversize {n = suc n} {xs = x ∷ xs} le = drop-oversize (≤-peel le)

split-take-drop : (n : ℕ) {xs : List A}
                → xs ＝ take n xs ++ drop n xs
split-take-drop  zero                 = refl
split-take-drop (suc n) {xs = []}     = refl
split-take-drop (suc n ){xs = x ∷ xs} = ap (x ∷_) (split-take-drop n)


-- span

span-append : ∀ (p : A → Bool) xs
            → let (ys , zs) = span p xs in
              xs ＝ ys ++ zs
span-append p []       = refl
span-append p (x ∷ xs) with p x
... | true  = ap (x ∷_) (span-append p xs)
... | false = refl

span-length : ∀ (p : A → Bool) xs
            → let (ys , zs) = span p xs in
              length xs ＝ length ys + length zs
span-length p xs =
  let (ys , zs) = span p xs in
  ap length (span-append p xs) ∙ ++-length ys zs

span-all : ∀ (p : A → Bool) xs
         → All (So ∘ p) (span p xs .fst)
span-all p []       = []
span-all p (x ∷ xs) with p x | recall p x
... | false | ⟪ e ⟫ = []
... | true  | ⟪ e ⟫ = subst So (e ⁻¹) oh ∷ (span-all p xs)


-- zip-with

zip-with-++ : {f : A → B → C}
            → {as bs : List A} {xs ys : List B}
            → length as ＝ length xs
            → zip-with f (as ++ bs) (xs ++ ys) ＝ zip-with f as xs ++ zip-with f bs ys
zip-with-++ {f} {as = []}     {xs = []}     e = refl
zip-with-++ {f} {as = []}     {xs = x ∷ xs} e = absurd (zero≠suc e)
zip-with-++ {f} {as = a ∷ as} {xs = []}     e = absurd (suc≠zero e)
zip-with-++ {f} {as = a ∷ as} {xs = x ∷ xs} e = ap (f a x ∷_) (zip-with-++ (suc-inj e))
