{-# OPTIONS --safe #-}
module Data.List.Operations.Properties where

open import Meta.Prelude
open import Meta.Effect
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
open import Data.Reflects.Properties
open import Data.Maybe.Base as Maybe
open import Data.Maybe.Path
open import Data.Maybe.Properties renaming (rec-fusion to rec-fusionᵐ)
open import Data.Maybe.Instances.Map.Properties
open import Data.List.Base as List
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Instances.Map
open import Data.List.Correspondences.Binary.Prefix
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
  xs ys : List A
  x y z w : A

-- rec

rec-++ : (z : B) (f : A → B → B) (xs ys : List A)
       → List.rec z f (xs ++ ys) ＝ List.rec (List.rec z f ys) f xs
rec-++ z f [] ys = refl
rec-++ z f (x ∷ xs) ys = ap (f x) (rec-++ z f xs ys)

-- TODO move to Data.List.Operations.Properties.Map ?
rec-map : {A : Type ℓ} {B : Type ℓ′}
          (z : C) (f : B → C → C) (h : A → B) (xs : List A)
        → List.rec z f (map h xs) ＝ List.rec z (f ∘ h) xs
rec-map z f h [] = refl
rec-map z f h (x ∷ xs) = ap (f (h x)) (rec-map z f h xs)

rec-fusion : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
             {z : B} {f : A → B → B} {g : A → C → C} {h : B → C}
             (xs : List A)
           → (∀ x y → h (f x y) ＝ g x (h y))
           → h (List.rec z f xs) ＝ List.rec (h z) g xs
rec-fusion             []       eq = refl
rec-fusion {z} {f} {g} (x ∷ xs) eq = eq x (List.rec z f xs) ∙ ap (g x) (rec-fusion xs eq)

-- length

length=0→nil : length xs ＝ 0 → xs ＝ []
length=0→nil {xs = []}     eq = refl
length=0→nil {xs = x ∷ xs} eq = false! eq

length=1→sng : length xs ＝ 1 → Σ[ x ꞉ A ] (xs ＝ x ∷ [])
length=1→sng {xs = []}     eq = false! eq
length=1→sng {xs = x ∷ xs} eq = x , ap (x ∷_) (length=0→nil (suc-inj eq))

length>0→Σ : 0 < length xs → Σ[ z ꞉ A ] (z ∈ₗ xs)
length>0→Σ {xs = []}     gt = false! gt
length>0→Σ {xs = x ∷ xs} _  = x , here refl

map-length : {A : Type ℓ} {B : Type ℓ′}
             {f : A → B} {xs : List A}
           → length (map f xs) ＝ length xs
map-length {f} {xs = []}     = refl
map-length {f} {xs = x ∷ xs} = ap suc (map-length {xs = xs})

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

opaque
  unfolding Prefix
  prefix-length : Prefix xs ys → length xs ≤ length ys
  prefix-length {xs} (ts , et) =
    subst (λ q → length xs ≤ length q) et $
    subst (length xs ≤_) (++-length xs ts ⁻¹) $
    ≤-+-r

opaque
  unfolding Prefix1
  prefix1-length : Prefix1 xs ys → length xs < length ys
  prefix1-length {xs} (t , ts , et) =
    subst (λ q → length xs < length q) et $
    subst (length xs <_) (+-comm (suc (length ts)) (length xs) ∙ ++-length xs (t ∷ ts) ⁻¹) $
    <-+-lr

-- !ᵐ

!ᵐ-ext : ∀ {A : Type ℓ} {xs ys : List A}
       → (∀ n → xs !ᵐ n ＝ ys !ᵐ n)
       → xs ＝ ys
!ᵐ-ext {xs = []}     {ys = []}     e = refl
!ᵐ-ext {xs = []}     {ys = y ∷ ys} e = false! (e 0)
!ᵐ-ext {xs = x ∷ xs} {ys = []}     e = false! (e 0)
!ᵐ-ext {xs = x ∷ xs} {ys = y ∷ ys} e =
  ap² {C = λ x xs → List _} _∷_
     (just-inj $ e 0)
     (!ᵐ-ext (e ∘ suc))

-- unconsᵐ / tailᵐ

unconsᵐ-∷ : ∀ {A : Type ℓ} {xs : List A}
          → xs ＝ Maybe.rec [] (_∷_ $²_) (unconsᵐ xs)
unconsᵐ-∷ {xs = []} = refl
unconsᵐ-∷ {xs = x ∷ xs} = refl

length-tailᵐ : ∀ {A : Type ℓ} {xs : List A}
             → length xs ＝ Maybe.rec zero (suc ∘ length) (tailᵐ xs)
length-tailᵐ {xs} =
    ap length unconsᵐ-∷
  ∙ rec-fusionᵐ {g = length} (unconsᵐ xs)
  ∙ mapₘ-rec {m = unconsᵐ xs} ⁻¹

-- snoc

snoc-append : (xs : List A) {x : A} → xs ∷r x ＝ xs ++ x ∷ []
snoc-append []       = refl
snoc-append (y ∷ xs) = ap (y ∷_) (snoc-append xs)

++-snoc : (xs ys : List A) (y : A) → xs ∷r y ++ ys ＝ xs ++ y ∷ ys
++-snoc []       ys y = refl
++-snoc (x ∷ xs) ys y = ap (x ∷_) (++-snoc xs ys y)

snoc-++ : (xs ys : List A) (y : A) → (xs ++ ys) ∷r y ＝ xs ++ ys ∷r y
snoc-++ []       ys y = refl
snoc-++ (x ∷ xs) ys y = ap (x ∷_) (snoc-++ xs ys y)

snoc-elim : (P : List A → 𝒰 ℓ′)
          → P []
          → (∀ xs x → P xs → P (xs ∷r x))
          → ∀ xs → P xs
snoc-elim P p[] ps xs = go [] xs p[]
  where
  go : ∀ xs ys → P xs → P (xs ++ ys)
  go xs []       pxs = subst P (sym $ ++-id-r xs) pxs
  go xs (y ∷ ys) pxs = subst P (++-snoc xs ys y) (go (snoc xs y) ys (ps xs y pxs))

snoc-length : (xs : List A) {x : A} → length (xs ∷r x) ＝ suc (length xs)
snoc-length xs {x} = ap length (snoc-append xs) ∙ ++-length xs (x ∷ []) ∙ +-comm (length xs) 1

snoc-inj : {xs ys : List A} {z w : A} → xs ∷r z ＝ ys ∷r w → (xs ＝ ys) × (z ＝ w)
snoc-inj {xs = []}     {ys = []}     e = refl , (∷-head-inj e)
snoc-inj {xs = []}     {ys = y ∷ ys} e = false! ⦃ Reflects-List-≠-tail ⦄ e
snoc-inj {xs = x ∷ xs} {ys = []}     e = false! ⦃ Reflects-List-≠-tail ⦄ e
snoc-inj {xs = x ∷ xs} {ys = y ∷ ys} e =
  first (ap² {C = λ _ _ → List _} _∷_ (∷-head-inj e)) $ snoc-inj (∷-tail-inj e)

all-∷r : {P : Pred A ℓ′} {xs : List A} → All P xs → P x → All P (xs ∷r x)
all-∷r {P} {xs} pxs px =
  subst (λ s → All P s) (snoc-append xs ⁻¹) $
  all-++ pxs (px ∷ [])

∷r-all : {P : Pred A ℓ′} {xs : List A} → All P (xs ∷r x) → All P xs × P x
∷r-all {P} {xs} axss =
  let (axs , px) = all-split {xs = xs} (subst (λ s → All P s) (snoc-append xs) axss) in
  axs , all-head px

any-∷r-init : {P : Pred A ℓ′} {xs : List A} {x : A}
            → Any P xs → Any P (xs ∷r x)
any-∷r-init {P} {xs} pxs =
  subst (λ q → Any P q) (snoc-append xs ⁻¹) (any-++-l pxs)

any-∷r-last : {P : Pred A ℓ′} {xs : List A} {x : A}
            → P x → Any P (xs ∷r x)
any-∷r-last {P} {xs} px =
  subst (λ q → Any P q) (snoc-append xs ⁻¹) (any-++-r (here px))

rec-∷r : {z : B} {f : A → B → B} {xs : List A} {x : A}
       → List.rec z f (xs ∷r x) ＝ List.rec (f x z) f xs
rec-∷r {z} {f} {xs} {x} =
    ap (List.rec z f) (snoc-append xs)
  ∙ rec-++ z f xs (x ∷ [])

map-∷r : ∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {f : A → B} {xs : List A} {x : A}
       → map f (xs ∷r x) ＝ map f xs ∷r f x
map-∷r {f} {xs} {x} =
    ap (map f) (snoc-append xs)
  ∙ map-++ f xs (x ∷ [])
  ∙ snoc-append (map f xs) ⁻¹

prefix-∷r-l : Prefix (xs ∷r x) ys → Prefix xs ys
prefix-∷r-l {xs} {ys} p =
  prefix-++-l $
  (subst (λ q → Prefix q ys) (snoc-append xs) $
   p)

-- reverse

reverse-++ : ∀ {xs ys : List A}
           → reverse (xs ++ ys) ＝ reverse ys ++ reverse xs
reverse-++ {xs = []}     {ys} = ++-id-r (reverse ys) ⁻¹
reverse-++ {xs = x ∷ xs} {ys} =
    ap (_++ x ∷ []) (reverse-++ {xs = xs})
  ∙ ++-assoc (reverse ys) (reverse xs) (x ∷ [])

reverse-∷r : ∀ {xs : List A} {x}
           → reverse (xs ∷r x) ＝ x ∷ reverse xs
reverse-∷r {xs} = ap reverse (snoc-append xs) ∙ reverse-++ {xs = xs}

reverse-inv : ∀ {xs : List A}
            → reverse (reverse xs) ＝ xs
reverse-inv {xs = []}     = refl
reverse-inv {xs = x ∷ xs} =
  reverse-++ {xs = reverse xs} ∙ ap (x ∷_) (reverse-inv {xs = xs})

reverse-length : ∀ {xs : List A}
               → length (reverse xs) ＝ length xs
reverse-length {xs = []}     = refl
reverse-length {xs = x ∷ xs} =
    ++-length (reverse xs) (x ∷ [])
  ∙ +-comm (length (reverse xs)) 1
  ∙ ap suc reverse-length

reverse-⊆ : ∀ {xs : List A}
           → xs ⊆ reverse xs
reverse-⊆ {xs = x ∷ xs} (here e)   = any-++-r {xs = reverse xs} (here e)
reverse-⊆ {xs = x ∷ xs} (there me) = any-++-l {xs = reverse xs} (reverse-⊆ me)

⊆-reverse : ∀ {xs : List A}
           → reverse xs ⊆ xs
⊆-reverse {xs = x ∷ xs} me with any-split {xs = reverse xs} me
... | inl m = there (⊆-reverse m)
... | inr (here e) = here e

reverse-≈ : ∀ {xs : List A}
          → xs ≈ reverse xs
reverse-≈ = reverse-⊆ , ⊆-reverse

-- head

head-map : ∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {xs : List A} {z} {f : A → B}
         → head (f z) (map f xs) ＝ f (head z xs)
head-map {xs = []}     = refl
head-map {xs = x ∷ xs} = refl

all→head : ∀ {xs x} {P : A → Type ℓ′}
         → P x → All P xs → P (head x xs)
all→head {xs = []}     px  _       = px
all→head {xs = x ∷ xs} _  (px ∷ _) = px

-- last

last-snoc : ∀ {xs : List A} {z x}
          → last z (xs ∷r x) ＝ x
last-snoc {xs = []}     = refl
last-snoc {xs = x ∷ xs} = last-snoc {xs = xs}

last-change : ∀ {xs : List A} {z w}
            → 0 < length xs
            → last z xs ＝ last w xs
last-change {xs = []}     0<l = false! 0<l
last-change {xs = x ∷ xs} 0<l = refl

last-reverse : ∀ {xs : List A} {z}
             → last z (reverse xs) ＝ head z xs
last-reverse {xs = []}         = refl
last-reverse {xs = x ∷ xs} {z} = ap (last z) (snoc-append (reverse xs) ⁻¹) ∙ last-snoc {xs = reverse xs}

head-last : ∀ {xs : List A} {z} → head (last z xs) xs ＝ head z xs
head-last {xs = []}     = refl
head-last {xs = x ∷ xs} = refl

head-reverse : ∀ {xs : List A} {z}
             → head z (reverse xs) ＝ last z xs
head-reverse {xs} {z} = last-reverse {xs = reverse xs} ⁻¹ ∙ ap (last z) (reverse-inv {xs = xs})

last-map : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {f : A → B} {xs : List A} {z : A}
         → last (f z) (map f xs) ＝ f (last z xs)
last-map {xs = []}     = refl
last-map {xs = x ∷ xs} = last-map {xs = xs}

last-elim : (P : List A → Type ℓ′)
          → P []
          → (∀ x xs → P xs → P (xs ∷r x))
          → ∀ xs → P xs
last-elim P h0 ih xs =
  subst P (++-id-l xs) $
  List.elim (λ q → ∀ w → P w → P (w ++ q))
            (λ w → subst P (++-id-r w ⁻¹))
            (λ y ys ihc w →
               subst P  (++-assoc w (y ∷ []) ys) ∘
               subst (λ q → P (q ++ ys)) (snoc-append w) ∘
               ihc (w ∷r y) ∘
               ih y w)
           xs [] h0

all→last : ∀ {xs x} {P : A → Type ℓ′}
         → P x → All P xs → P (last x xs)
all→last {xs = []}     px  _        = px
all→last {xs = x ∷ xs} _  (px ∷ ax) = all→last px ax

-- fold-l

foldl-rev : (z : B) (f : B → A → B) (xs : List A)
           → fold-l f z (reverse xs) ＝ List.rec z (flip f) xs
foldl-rev z f xs =
  snoc-elim (λ q → ∀ z′ → fold-l f z′ (reverse q) ＝ List.rec z′ (flip f) q)
    (λ _ → refl)
    (λ xs x ih z′ →   ap (fold-l f z′) (reverse-∷r {xs = xs})
                    ∙ ih (f z′ x)
                    ∙ rec-++ z′ (flip f) xs (x ∷ []) ⁻¹
                    ∙ ap (List.rec z′ (flip f)) (snoc-append xs ⁻¹))
     xs z

foldl-++ : (z : B) (f : B → A → B) (xs ys : List A)
         → fold-l f z (xs ++ ys) ＝ fold-l f (fold-l f z xs) ys
foldl-++ z f xs ys =
    ap (fold-l f z) (reverse-inv {xs = xs ++ ys} ⁻¹)
  ∙ foldl-rev z f (reverse (xs ++ ys))
  ∙ ap (List.rec z (flip f)) (reverse-++ {xs = xs})
  ∙ rec-++ z (flip f) (reverse ys) (reverse xs)
  ∙ foldl-rev (List.rec z (λ b a → f a b) (reverse xs)) f (reverse ys) ⁻¹
  ∙ ap (fold-l f (List.rec z (flip f) (reverse xs))) (reverse-inv {xs = ys})
  ∙ ap (λ q → fold-l f q ys) (foldl-rev z f (reverse xs) ⁻¹ ∙ ap (fold-l f z) (reverse-inv {xs = xs}))

foldl-∷r : (z : B) (f : B → A → B) (xs : List A) (x : A)
         → fold-l f z (xs ∷r x) ＝ f (fold-l f z xs) x
foldl-∷r z f xs x = ap (fold-l f z) (snoc-append xs) ∙ foldl-++ z f xs (x ∷ [])

-- reverse-fast

reverse=reverse-fast : (xs : List A) → reverse xs ＝ reverse-fast xs
reverse=reverse-fast =
  snoc-elim (λ q → reverse q ＝ reverse-fast q)
    refl
    (λ xs x ih → reverse-∷r {xs = xs} ∙ ap (x ∷_) ih ∙ foldl-∷r [] (λ b a → a ∷ b) xs x ⁻¹)

-- all

all?-++ : ∀ {p : A → Bool} {xs ys : List A}
        → all p (xs ++ ys) ＝ all p xs and all p ys
all?-++     {xs = []}          = refl
all?-++ {p} {xs = x ∷ xs} {ys} =
    ap (p x and_) (all?-++ {xs = xs})
  ∙ and-assoc (p x) (all p xs) (all p ys) ⁻¹

all?-map : ∀ {A : Type ℓ} {B : Type ℓ′}
             {p : B → Bool} {f : A → B} {xs : List A}
         → all p (map f xs) ＝ all (p ∘ f) xs
all?-map {p} {f} {xs} =
  ap (List.rec true _and_)
     (happly (map-pres-comp ⁻¹) xs)

all?-or : ∀ {b} {p : A → Bool} {xs : List A}
        → all (λ x → b or p x) xs ＝ b or all p xs
all?-or {b}     {xs = []}     = or-absorb-r b ⁻¹
all?-or {b} {p} {xs = x ∷ xs} =
    ap ((b or p x) and_) (all?-or {p = p} {xs = xs})
  ∙ or-distrib-and-l b (p x) (all p xs) ⁻¹

not-all? : ∀ {p : A → Bool} {xs : List A}
        → not (all p xs) ＝ any (not ∘ p) xs
not-all?     {xs = []}     = refl
not-all? {p} {xs = x ∷ xs} =
    not-and (p x) _
  ∙ ap (not (p x) or_) (not-all? {xs = xs})

-- any

any?-++ : ∀ {p : A → Bool} {xs ys : List A}
        → any p (xs ++ ys) ＝ any p xs or any p ys
any?-++ {xs = []} = refl
any?-++ {p} {xs = x ∷ xs} {ys} =
    ap (p x or_) (any?-++ {xs = xs})
  ∙ or-assoc (p x) (any p xs) (any p ys) ⁻¹

not-any? : ∀ {p : A → Bool} {xs : List A}
        → not (any p xs) ＝ all (not ∘ p) xs
not-any?     {xs = []}     = refl
not-any? {p} {xs = x ∷ xs} =
    not-or (p x) _
  ∙ ap (not (p x) and_) (not-any? {xs = xs})

--TODO move these 2 somewhere
¬Any→All¬ : {xs : List A} {P : A → 𝒰 ℓ′}
          → ¬ Any P xs → All (λ x → ¬ (P x)) xs
¬Any→All¬ {xs = []}     na = []
¬Any→All¬ {xs = x ∷ xs} na = contra here na ∷ ¬Any→All¬ (contra there na)

Any¬→¬All : {xs : List A} {P : A → 𝒰 ℓ′}
          → Any (λ x → ¬ (P x)) xs → ¬ All P xs
Any¬→¬All {xs = x ∷ xs} (here npx) (px ∷ a) = npx px
Any¬→¬All {xs = x ∷ xs} (there an) (px ∷ a) = Any¬→¬All an a

-- replicate

length-replicate : length (replicate n z) ＝ n
length-replicate {n = zero}  = refl
length-replicate {n = suc n} = ap suc (length-replicate {n = n})

replicate-+ : replicate (n + m) z ＝ replicate n z ++ replicate m z
replicate-+ {n = zero}      = refl
replicate-+ {n = suc n} {z} = ap (z ∷_) (replicate-+ {n = n})

replicate-snoc : replicate (suc n) z ＝ snoc (replicate n z) z
replicate-snoc {n} {z} = ap (λ q → replicate q z) (+-comm 1 n) ∙ replicate-+ {m = 1} ∙ snoc-append _ ⁻¹

replicate-all : (n : ℕ)
              → All (_＝ z) (replicate n z)
replicate-all  zero   = []
replicate-all (suc n) = refl ∷ replicate-all n

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

filter-++ : ∀ {p : A → Bool} (xs : List A) {ys}
          → filter p (xs ++ ys) ＝ filter p xs ++ filter p ys
filter-++     [] = refl
filter-++ {p} (x ∷ xs) with p x
... | true  = ap (x ∷_) (filter-++ xs)
... | false = filter-++ xs

-- TODO generalize to subsets
all→filter : {P : A → 𝒰 ℓ′} {p : A → Bool} {xs : List A}
           → All P xs → All P (filter p xs)
all→filter         {xs = []}     []       = []
all→filter {P} {p} {xs = x ∷ xs} (px ∷ a) with p x
... | true  = px ∷ all→filter a
... | false = all→filter a

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

Reflects-filter-all : {p : A → Bool} {xs : List A}
                    → Reflects (filter p xs ＝ xs) (all p xs)
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

∈-filter : ∀ {p} {z : A} {xs}
          → ⌞ p z ⌟ → z ∈ xs
          → z ∈ filter p xs
∈-filter {p} {xs = x ∷ xs} pz ixs with p x | recall p x
∈-filter                   pz (here e)    | true  | _      = here e
∈-filter                   pz (there ixs) | true  | _      =
  there (∈-filter pz ixs)
∈-filter {p}               pz (here e)    | false | ⟪ eq ⟫ =
  false! $ (so≃is-true $ pz) ⁻¹ ∙ ap p e ∙ eq
∈-filter                   pz (there ixs) | false | _      =
  ∈-filter pz ixs

filter-∈ : ∀ {p} {z : A} {xs}
          → z ∈ filter p xs
          → ⌞ p z ⌟ × z ∈ xs
filter-∈     {xs = []}     pf = false! pf
filter-∈ {p} {xs = x ∷ xs} pf with p x | recall p x
filter-∈ {p} {xs = x ∷ xs} pf         | false | ⟪ eq ⟫ =
  second there (filter-∈ {xs = xs} pf)
filter-∈ {p} {xs = x ∷ xs} (here e)   | true | ⟪ eq ⟫ =
  (so≃is-true ⁻¹ $ ap p e ∙ eq) , here e
filter-∈ {p} {xs = x ∷ xs} (there pf) | true | ⟪ eq ⟫ =
  second there (filter-∈ {xs = xs} pf)

filter-and : ∀ {p1 p2 : A → Bool} {xs}
           → filter (λ q → p1 q and p2 q) xs ＝ filter p1 (filter p2 xs)
filter-and           {xs = []}     = refl
filter-and {p1} {p2} {xs = x ∷ xs} with p2 x
... | true  = ap² (λ a b → if a then x ∷ b else b) (and-id-r (p1 x)) (filter-and {xs = xs})
... | false = if-false (subst (So ∘ not) (and-absorb-r (p1 x) ⁻¹) oh) ∙ filter-and {xs = xs}

filter-comm : ∀ {p1 p2 : A → Bool} {xs}
           → filter p1 (filter p2 xs) ＝ filter p2 (filter p1 xs)
filter-comm {p1} {p2} {xs} =
    filter-and {xs = xs} ⁻¹
  ∙ ap (λ q → filter q xs) (fun-ext λ q → and-comm (p1 q) (p2 q))
  ∙ filter-and {xs = xs}

filter-OPE : {p : A → Bool} {xs : List A}
           → OPE (filter p xs) xs
filter-OPE     {xs = []}     = odone
filter-OPE {p} {xs = x ∷ xs} with p x
... | true  = otake refl filter-OPE
... | false = odrop filter-OPE

{-
filter-size-neg : {p : A → Bool} {s : List A} {z : A}
                → ⌞ not (p z) ⌟ → z ∈ s → length (filter p s) < length s
filter-size-neg {s = x ∷ s} npz (here e) = {!!}
filter-size-neg {s = x ∷ s} npz (there zin) = {!!}
-}

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

count<length : ∀ (p : A → Bool) xs
             → Any (So ∘ not ∘ p) xs
             → count p xs < length xs
count<length p xs an =
  ≤→<⊎= (count≤length p xs) &
  [ id
  , (λ e → absurd (Any¬→¬All (any-map so-not an) (count→all p xs e))) ]ᵤ

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


-- zip / zip-with / unzip

zip-with-++ : {f : A → B → C}
            → {as bs : List A} {xs ys : List B}
            → length as ＝ length xs
            → zip-with f (as ++ bs) (xs ++ ys) ＝ zip-with f as xs ++ zip-with f bs ys
zip-with-++     {as = []}     {xs = []}     _ = refl
zip-with-++     {as = []}     {xs = x ∷ xs} e = false! e
zip-with-++     {as = a ∷ as} {xs = []}     e = false! e
zip-with-++ {f} {as = a ∷ as} {xs = x ∷ xs} e = ap (f a x ∷_) (zip-with-++ (suc-inj e))

-- TODO coalesce decminmax stuff?
module _ where
  open decminmax ℕ-dec-total
  open decminmaxprops ℕ-dec-total ℕ-dec-total

  zip-with-length : ∀ {xs ys} {f : A → B → C}
                  → length (zip-with f xs ys) ＝ min (length xs) (length ys)
  zip-with-length {xs = []}     {ys = []}     = refl
  zip-with-length {xs = []}     {ys = y ∷ ys} = refl
  zip-with-length {xs = x ∷ xs} {ys = []}     = refl
  zip-with-length {xs = x ∷ xs} {ys = y ∷ ys} =
      ap suc zip-with-length
    ∙ min-ap Suc (length xs) (length ys)

∈-zip-with-l : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
                {f : A → B → C} {as : List A} {bs : List B} {a : A}
              → length as ＝ length bs
              → a ∈ as
              → Σ[ b ꞉ B ] (b ∈ bs) × (f a b ∈ zip-with f as bs)
∈-zip-with-l     {as = a ∷ as} {bs = []}     e  a∈        = false! e
∈-zip-with-l {f} {as = a ∷ as} {bs = b ∷ bs} _ (here ae)   =
  b , here refl , here (ap (λ q → f q b) ae)
∈-zip-with-l {f} {as = a ∷ as} {bs = b ∷ bs} e (there a∈) =
  let (b , b∈ , fab∈) = ∈-zip-with-l {f = f} (suc-inj e) a∈ in
  b , there b∈ , there fab∈

∈-zip-with-r : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
                {f : A → B → C} {as : List A} {bs : List B} {b : B}
              → length as ＝ length bs
              → b ∈ bs
              → Σ[ a ꞉ A ] (a ∈ as) × (f a b ∈ zip-with f as bs)
∈-zip-with-r     {as = []}     {bs = b ∷ bs} e  b∈        = false! e
∈-zip-with-r {f} {as = a ∷ as} {bs = b ∷ bs} e (here be)   =
  a , here refl , here (ap (f a) be)
∈-zip-with-r {f} {as = a ∷ as} {bs = b ∷ bs} e (there b∈) =
  let (a , a∈ , fab∈) = ∈-zip-with-r {f = f} (suc-inj e) b∈ in
  a , there a∈ , there fab∈

zip-with-∈ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
             {f : A → B → C} {as : List A} {bs : List B} {c : C}
           → c ∈ zip-with f as bs
           → Σ[ a ꞉ A ] Σ[ b ꞉ B ] ((a ∈ as) × (b ∈ bs) × (c ＝ f a b))
zip-with-∈ {as = []}     {bs = []}     c∈         = false! c∈
zip-with-∈ {as = []}     {bs = b ∷ bs} c∈         = false! c∈
zip-with-∈ {as = a ∷ as} {bs = []}     c∈         = false! c∈
zip-with-∈ {as = a ∷ as} {bs = b ∷ bs} (here ce)  =
  a , b , here refl , here refl , ce
zip-with-∈ {as = a ∷ as} {bs = b ∷ bs} (there c∈) =
  let (a′ , b′ , a∈ , b∈ , ce) = zip-with-∈ {as = as} c∈ in
  a′ , b′ , there a∈ , there b∈ , ce

unzip-∷-l : ∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {a : A} {abs as bs}
          → unzip abs ＝ (a ∷ as , bs)
          → Σ[ b ꞉ B ] Σ[ bs′ ꞉ List B ] Σ[ abs′ ꞉ List (A × B) ] (b ∷ bs′ ＝ bs) × (abs ＝ (a , b) ∷ abs′)
unzip-∷-l {abs = []}                            e = false! (×-path-inv e .fst)
unzip-∷-l {abs = (a′ , b) ∷ abs}  {bs = []}     e = false! (×-path-inv e .snd)
unzip-∷-l {abs = (a′ , b′) ∷ abs} {bs = b ∷ bs} e =
  let (e1 , e2) = ×-path-inv e in
  b , bs , abs , refl , (ap (_∷ abs) (×-path (∷-head-inj e1) (∷-head-inj e2)))

unzip-zip : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
            {xs : List A}  {ys : List B}
          → length xs ＝ length ys
          → unzip (zip xs ys) ＝ (xs , ys)
unzip-zip {xs = []}     {ys = []}     e = refl
unzip-zip {xs = []}     {ys = y ∷ ys} e = false! e
unzip-zip {xs = x ∷ xs} {ys = []}     e = false! e
unzip-zip {xs = x ∷ xs} {ys = y ∷ ys} e =
  let xye = ×-path-inv $ unzip-zip {xs = xs} {ys = ys} (suc-inj e) in
  ×-path (ap (x ∷_) (xye .fst)) (ap (y ∷_) (xye .snd))

zip-unzip : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
            {xys : List (A × B)}
          → let (xs , ys) = unzip xys in
            zip xs ys ＝ xys
zip-unzip {xys = []}            = refl
zip-unzip {xys = (x , y) ∷ xys} = ap ((x , y) ∷_) (zip-unzip {xys = xys})

-- count-from-to

count-from-to-idem : {n : ℕ}
                   → count-from-to n n ＝ []
count-from-to-idem {n = zero}  = refl
count-from-to-idem {n = suc n} = ap (map suc) (count-from-to-idem {n = n})

count-from-to-suc-l : {m n : ℕ}
                    → m < n
                    → count-from-to m n ＝ m ∷ count-from-to (suc m) n
count-from-to-suc-l {m = m}     {n = zero}  m<n = false! m<n
count-from-to-suc-l {m = zero}  {n = suc n} m<n = refl
count-from-to-suc-l {m = suc m} {n = suc n} m<n =
  ap (map suc) (count-from-to-suc-l {m = m} {n = n} (<-peel m<n))

count-from-to-suc-r : {m n : ℕ}
                    → m ≤ n
                    → count-from-to m (suc n) ＝ count-from-to m n ∷r n
count-from-to-suc-r {m = zero} {n = zero} _ = refl
count-from-to-suc-r {m = suc m} {n = zero} m≤n = false! m≤n
count-from-to-suc-r {m = zero} {n = suc n} m≤n =
  ap (0 ∷_) (ap (map suc) (count-from-to-suc-r {m = 0} {n = n} z≤) ∙ map-∷r)
count-from-to-suc-r {m = suc m} {n = suc n} m≤n =
  ap (map suc) (count-from-to-suc-r {m = m} {n = n} (≤-peel m≤n)) ∙ map-∷r

-- TODO more arithmetics

count-from-to-len : {m n : ℕ}
                  → length (count-from-to m n) ＝ n ∸ m
count-from-to-len {m = m}     {n = zero}  = ∸-zero-l m ⁻¹
count-from-to-len {m = zero}  {n = suc n} = ap suc (map-length ∙ count-from-to-len {m = 0} {n = n})
count-from-to-len {m = suc m} {n = suc n} = map-length ∙ count-from-to-len {m = m} {n = n}

count-from-to-∈ : {m n k : ℕ}
                  → k ∈ count-from-to m n
                  → (m ≤ k) × (k < n)
count-from-to-∈ {m = zero} {n = suc n} (here e)   =
  z≤ , subst (_< suc n) (e ⁻¹) z<s
count-from-to-∈ {m = zero} {n = suc n} (there k∈) =
  let (l , l∈ , le) = map-∈Σ suc k∈
      ih< = count-from-to-∈ l∈ .snd
    in
  z≤ , subst (_< suc n) (le ⁻¹) (s<s ih<)
count-from-to-∈ {m = suc m} {n = suc n} k∈ =
  let (l , l∈ , le) = map-∈Σ suc k∈
      (ih≤ , ih<) = count-from-to-∈ {m = m} {n = n} l∈
    in
  subst (λ q → (suc m ≤ q) × (q < suc n)) (le ⁻¹) $
  (s≤s ih≤) , (s<s ih<)

∈-count-from-to : {m n k : ℕ}
                 → m ≤ k → k < n
                 → k ∈ count-from-to m n
∈-count-from-to             {n = zero}              _   k<n = false! k<n
∈-count-from-to {m = zero}  {n = suc n} {k = zero}  _   _   = here refl
∈-count-from-to {m = zero}  {n = suc n} {k = suc k} _   k<n =
  there (∈-map suc (∈-count-from-to {m = 0} {n = n} {k = k} z≤ (<-peel k<n)))
∈-count-from-to {m = suc m} {n = suc n} {k = zero}  m≤k _   = false! m≤k
∈-count-from-to {m = suc m} {n = suc n} {k = suc k} m≤k k<n =
  ∈-map suc (∈-count-from-to {m = m} {n = n} {k = k} (≤-peel m≤k) (<-peel k<n))

-- TODO ≃
