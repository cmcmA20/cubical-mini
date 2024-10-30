{-# OPTIONS --safe #-}
module Data.List.Operations.Properties where

open import Meta.Prelude
open import Foundations.Base

open import Logic.Decidability
open import Logic.Discreteness

open import Order.Constructions.Minmax
open import Order.Constructions.Nat

open import Data.Empty as Empty
open import Data.Bool.Base as Bool
open import Data.Bool.Path
open import Data.Bool.Properties
open import Data.Sum.Base as Sum
open import Data.Dec.Base as Dec
open import Data.Reflects.Base as Reflects
open import Data.List.Base as List
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Binary.OPE
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Two
open import Data.Nat.Two.Properties
open import Data.Nat.Order.Base
open import Data.Nat.Properties

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  m n : ℕ
  xs : List A
  x y z w : A

-- length

length=0→nil : length xs ＝ 0 → xs ＝ []
length=0→nil {xs = []}     eq = refl
length=0→nil {xs = x ∷ xs} eq = false! eq

length=1→sng : length xs ＝ 1 → Σ[ x ꞉ A ] (xs ＝ x ∷ [])
length=1→sng {xs = []}     eq = false! eq
length=1→sng {xs = x ∷ xs} eq = x , ap (x ∷_) (length=0→nil (suc-inj eq))

++-length : (xs ys : List A) → length (xs ++ ys) ＝ length xs + length ys
++-length []       ys = refl
++-length (x ∷ xs) ys = ap suc (++-length xs ys)

++-same-inj : (as xs : List A) {bs ys : List A}
            → length as ＝ length xs
            → as ++ bs ＝ xs ++ ys
            → (as ＝ xs) × (bs ＝ ys)
++-same-inj     []       []       el e = refl , e
++-same-inj     []       (x ∷ xs) el e = false! el
++-same-inj     (a ∷ as) []       el e = false! el
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
snoc-inj {xs = []}     {ys = []}     e = refl , (∷-head-inj e)
snoc-inj {xs = []}     {ys = y ∷ ys} e = false! ⦃ Reflects-List-≠-tail ⦄ e
snoc-inj {xs = x ∷ xs} {ys = []}     e = false! ⦃ Reflects-List-≠-tail ⦄ e
snoc-inj {xs = x ∷ xs} {ys = y ∷ ys} e =
  first (ap² {C = λ _ _ → List _} _∷_ (∷-head-inj e)) $ snoc-inj (∷-tail-inj e)


-- all

Reflects-all-bool : {p : A → Bool} {xs : List A}
                  → Reflects (All (So ∘ p) xs) (all p xs)
Reflects-all-bool     {xs = []}     = ofʸ []
Reflects-all-bool {p} {xs = x ∷ xs} =
  Reflects.dmap
    (_∷_ $ₜ²_)
    (contra (λ where (px ∷ ps) → px , ps))
    (Reflects-× ⦃ rp = Reflects-So ⦄ ⦃ rq = Reflects-all-bool {xs = xs} ⦄)

-- TODO `Decidable P` doesn't work
Reflects-all-dec : {xs : List A} {P : A → 𝒰 ℓ′} (P? : ∀ x → Dec (P x))
                 → Reflects (All P xs) (all (⌊_⌋ ∘ P?) xs)
Reflects-all-dec {xs = []}     P? = ofʸ []
Reflects-all-dec {xs = x ∷ xs} P? =
  Reflects.dmap
    (_∷_ $ₜ²_)
    (contra (λ where (px ∷ ps) → px , ps))
    (Reflects-× ⦃ rp = reflects-does (P? x) ⦄ ⦃ rq = Reflects-all-dec {xs = xs} P? ⦄)


all?-++ : ∀ {p : A → Bool} {xs ys : List A}
        → all p (xs ++ ys) ＝ all p xs and all p ys
all?-++ {p} {xs = []}     {ys} = refl
all?-++ {p} {xs = x ∷ xs} {ys} = ap (p x and_) (all?-++ {xs = xs}) ∙ and-assoc (p x) (all p xs) (all p ys) ⁻¹

-- any

Reflects-any-bool : {p : A → Bool} {xs : List A}
                  → Reflects (Any (So ∘ p) xs) (any p xs)
Reflects-any-bool {xs = []}     = ofⁿ false!
Reflects-any-bool {xs = x ∷ xs} =
  Reflects.dmap
   [ here , there ]ᵤ
   (contra (λ where
               (here px) → inl px
               (there ax) → inr ax))
   (Reflects-⊎ ⦃ rp = Reflects-So ⦄ ⦃ rq = Reflects-any-bool {xs = xs} ⦄)

Reflects-any-dec : {xs : List A} {P : A → 𝒰 ℓ′} (P? : ∀ x → Dec (P x))
                 → Reflects (Any P xs) (any (⌊_⌋ ∘ P?) xs)
Reflects-any-dec {xs = []}     P? = ofⁿ false!
Reflects-any-dec {xs = x ∷ xs} P? =
  Reflects.dmap
   [ here , there ]ᵤ
   (contra (λ where
               (here px) → inl px
               (there ax) → inr ax))
   (Reflects-⊎ ⦃ rp = reflects-does (P? x) ⦄ ⦃ rq = Reflects-any-dec {xs = xs} P? ⦄)

-- replicate

replicate-+ : replicate (n + m) z ＝ replicate n z ++ replicate m z
replicate-+ {n = zero}      = refl
replicate-+ {n = suc n} {z} = ap (z ∷_) (replicate-+ {n = n})

replicate-snoc : replicate (suc n) z ＝ snoc (replicate n z) z
replicate-snoc {n} {z} = ap (λ q → replicate q z) (+-comm 1 n) ∙ replicate-+ {m = 1} ∙ snoc-append _ ⁻¹

All-replicate : (xs : List A)
              → All (_＝ z) xs
              → xs ＝ replicate (length xs) z
All-replicate     []       []       = refl
All-replicate {z} (x ∷ xs) (xa ∷ a) = ap² List._∷_ xa (All-replicate xs a)


-- filter

filter-false : (xs : List A)
             → filter (λ _ → false) xs ＝ []
filter-false []       = refl
filter-false (x ∷ xs) = filter-false xs

filter-true : (xs : List A)
             → filter (λ _ → true) xs ＝ xs
filter-true []       = refl
filter-true (x ∷ xs) = ap (x ∷_) (filter-true xs)

-- TODO generalize to subsets
all→filter : {P : A → 𝒰 ℓ′} {p : A → Bool} {xs : List A}
           → All P xs → All P (filter p xs)
all→filter         {xs = []}     []       = []
all→filter {P} {p} {xs = x ∷ xs} (px ∷ a) =
  Bool.elim
    {P = λ q → All P (if q then x ∷ filter p xs else filter p xs)}
    (px ∷ all→filter a)
    (all→filter a)
    (p x)

all-filter : {p : A → Bool} {xs : List A}
           → ⌞ all p (filter p xs) ⌟
all-filter {p} {xs = []}     = Oh
all-filter {p} {xs = x ∷ xs} =
  Bool.elim
    {P = λ q → p x ＝ q → ⌞ all p (if q then x ∷ filter p xs else filter p xs) ⌟}
    (λ e → (so≃is-true ⁻¹ $ e) × all-filter {xs = xs})
    (λ _ → all-filter {xs = xs})
    (p x) refl

filter-all : {p : A → Bool} {xs : List A}
           → ⌞ all p xs ⌟ → filter p xs ＝ xs
filter-all {p = p} {xs = []}     _ = refl
filter-all {p = p} {xs = x ∷ xs} s =
  let pax = and-so-≃ {x = p x} $ s in
  subst (λ q → (if q then x ∷ filter p xs else filter p xs) ＝ x ∷ xs) ((so≃is-true $ pax .fst) ⁻¹) $
  ap (x ∷_) (filter-all (pax .snd))

Reflects-filter-all : {p : A → Bool} {xs : List A} → Reflects (filter p xs ＝ xs) (all p xs)
Reflects-filter-all {p} {xs} =
  Reflects.dmap filter-all
    (contra λ e → subst (So ∘ all p) e (all-filter {xs = xs}))
    Reflects-So

filter-has-eq : {p1 p2 : A → Bool} {xs : List A}
             → (∀ x → x ∈ xs → p1 x ＝ p2 x)
             → filter p1 xs ＝ filter p2 xs
filter-has-eq {xs = []}     eqp = refl
filter-has-eq {xs = x ∷ xs} eqp =
  ap² (λ a b → if a then x ∷ b else b)
      (eqp x (here refl))
      (filter-has-eq {xs = xs} λ q hq → eqp q (there hq))

filter-OPE : {p : A → Bool} {xs : List A}
           → OPE (filter p xs) xs
filter-OPE     {xs = []}     = odone
filter-OPE {p} {xs = x ∷ xs} =
  Bool.elim
    {P = λ q → OPE (if q then x ∷ filter p xs else filter p xs) (x ∷ xs)}
    (otake refl filter-OPE)
    (odrop filter-OPE)
    (p x)

-- count

count-++ : ∀ (p : A → Bool) xs ys
         → count p (xs ++ ys) ＝ count p xs + count p ys
count-++ p []       ys = refl
count-++ p (x ∷ xs) ys =
    ap (bit (p x) +_) (count-++ p xs ys)
  ∙ +-assoc (bit (p x)) (count p xs) (count p ys)

Reflects-0<count : ∀ (p : A → Bool) xs
                 → Reflects (0 < count p xs) (any p xs)
Reflects-0<count p []       = ofⁿ false!
Reflects-0<count p (x ∷ xs) with p x
... | false = Reflects-0<count p xs
... | true  = ofʸ z<s

length-filter : ∀ (p : A → Bool) xs
              → length (filter p xs) ＝ count p xs
length-filter p []       = refl
length-filter p (x ∷ xs) with p x
... | false = length-filter p xs
... | true  = ap suc (length-filter p xs)

count≤length : ∀ (p : A → Bool) xs
             → count p xs ≤ length xs
count≤length p []       = z≤
count≤length p (x ∷ xs) with p x
... | false = ≤-suc-r (count≤length p xs)
... | true  = s≤s (count≤length p xs)

count→all : ∀ (p : A → Bool) xs
          → count p xs ＝ length xs → All (So ∘ p) xs
count→all p []       e = []
count→all p (x ∷ xs) e with p x | recall p x
... | false | ⟪ eq ⟫ = absurd (suc≰id $ subst (_≤ length xs) e $ count≤length p xs)
... | true  | ⟪ eq ⟫ = (so≃is-true ⁻¹ $ eq) ∷ count→all p xs (suc-inj e)

all→count : ∀ (p : A → Bool) xs
          → All (So ∘ p) xs → count p xs ＝ length xs
all→count p []       []       = refl
all→count p (x ∷ xs) (px ∷ a) =
  subst (λ q → bit q + count p xs ＝ suc (length xs))
        ((so≃is-true $ px) ⁻¹)
        (ap suc (all→count p xs a))

count-union-inter : ∀ p1 p2 (xs : List A)
                  → count (λ x → p1 x or p2 x) xs + count (λ x → p1 x and p2 x) xs ＝ count p1 xs + count p2 xs
count-union-inter p1 p2 []       = refl
count-union-inter p1 p2 (x ∷ xs) =
    +-interchange (bit (p1 x or p2 x)) (count (λ x → p1 x or p2 x) xs) (bit (p1 x and p2 x)) (count (λ x → p1 x and p2 x) xs)
  ∙ ap (bit (p1 x or p2 x) + bit (p1 x and p2 x) +_) (count-union-inter p1 p2 xs)
  ∙ ap (_+ (count p1 xs + count p2 xs))
       (Bool.elim
          {P = λ q → bit (q or p2 x) + bit (q and p2 x)
                   ＝ bit q + bit (p2 x)}
          refl
          (+-zero-r (bit (p2 x)))
          (p1 x))
  ∙ +-interchange (bit (p1 x)) (count p1 xs) (bit (p2 x)) (count p2 xs) ⁻¹

count-false : (xs : List A)
            → count (λ _ → false) xs ＝ 0
count-false xs = length-filter (λ _ → false) xs ⁻¹ ∙ ap length (filter-false xs)

count-true : (xs : List A)
           → count (λ _ → true) xs ＝ length xs
count-true xs = length-filter (λ _ → true) xs ⁻¹ ∙ ap length (filter-true xs)

-- find

find≤length : ∀ (p : A → Bool) xs
            → count p xs ≤ length xs
find≤length p [] = z≤
find≤length p (x ∷ xs) with p x
... | false = ≤-suc-r (find≤length p xs)
... | true  = s≤s (find≤length p xs)

-- take & drop

take-nil : take n (the (List A) []) ＝ []
take-nil {n = zero}  = refl
take-nil {n = suc _} = refl

drop-nil : drop n (the (List A) []) ＝ []
drop-nil {n = zero}  = refl
drop-nil {n = suc _} = refl

module _ where
  open decminmax ℕ-dec-total
  open decminmaxprops ℕ-dec-total ℕ-dec-total


  length-take : length (take n xs) ＝ min n (length xs)
  length-take {n = zero}                = refl
  length-take {n = suc n} {xs = []}     = refl
  length-take {n = suc n} {xs = x ∷ xs} = ap suc length-take ∙ min-ap Suc n (length xs)

length-drop : length (drop n xs) ＝ length xs ∸ n
length-drop {n = zero}                = refl
length-drop {n = suc n} {xs = []}     = refl
length-drop {n = suc n} {xs = x ∷ xs} = length-drop {n = n}

take-+ : take (n + m) xs ＝ take n xs ++ take m (drop n xs)
take-+ {n = zero}                = refl
take-+ {n = suc n} {xs = []}     = take-nil ⁻¹
take-+ {n = suc n} {xs = x ∷ xs} = ap (x ∷_) (take-+ {n = n})

drop-+ : drop (n + m) xs ＝ drop m (drop n xs)
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
split-take-drop (suc n) {xs = x ∷ xs} = ap (x ∷_) (split-take-drop n)


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
zip-with-++     {as = []}     {xs = []}     _ = refl
zip-with-++     {as = []}     {xs = x ∷ xs} e = false! e
zip-with-++     {as = a ∷ as} {xs = []}     e = false! e
zip-with-++ {f} {as = a ∷ as} {xs = x ∷ xs} e = ap (f a x ∷_) (zip-with-++ (suc-inj e))
