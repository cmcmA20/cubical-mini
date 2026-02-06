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
open import Data.Maybe.Instances.Map
open import Data.Maybe.Instances.Map.Properties
open import Data.Maybe.Correspondences.Unary.Any renaming (Any to Anyᵐ ; any-map to any-mapᵐ ; Reflects-any-bool to Reflects-Anyᵐ-bool)
open import Data.Maybe.Membership
open import Data.List.Base as List
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.At
open import Data.List.Membership as List
open import Data.List.Instances.Map
open import Data.List.Correspondences.Unary.Pairwise
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

rec-id : {xs : List A}
       → List.rec [] _∷_ xs ＝ xs
rec-id {xs = []}     = refl
rec-id {xs = x ∷ xs} = ap (x ∷_) rec-id

rec-++ : (z : B) (f : A → B → B) (xs ys : List A)
       → List.rec z f (xs ++ ys) ＝ List.rec (List.rec z f ys) f xs
rec-++ z f [] ys = refl
rec-++ z f (x ∷ xs) ys = ap (f x) (rec-++ z f xs ys)

-- TODO move to Data.List.Operations.Properties.Map ?
rec-map : {A : Type ℓ} {B : Type ℓ′}
          (z : C) (f : B → C → C) (h : A → B) (xs : List A)
        → List.rec z f (map h xs) ＝ List.rec z (f ∘ h) xs
rec-map z f h []       = refl
rec-map z f h (x ∷ xs) = ap (f (h x)) (rec-map z f h xs)

rec-fusion : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
             {z : B} {f : A → B → B} {g : A → C → C} {h : B → C}
           → (∀ x y → h (f x y) ＝ g x (h y))
           → (xs : List A)
           → h (List.rec z f xs) ＝ List.rec (h z) g xs
rec-fusion             eq []       = refl
rec-fusion {z} {f} {g} eq (x ∷ xs) =
    eq x (List.rec z f xs)
  ∙ ap (g x) (rec-fusion eq xs)

-- TODO lemmas when f is associative/commutative

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

++=[]-2 : (xs ys : List A) → xs ++ ys ＝ [] → (xs ＝ []) × (ys ＝ [])
++=[]-2 xs ys e =
  ++-same-inj xs []
    (+=0-2 (length xs) _ (++-length xs _ ⁻¹ ∙ ap length e) .fst)
    e

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

any→ℕ≤length : {P : Pred A ℓ′} {xs : List A}
               (a : Any P xs) → any→ℕ a < length xs
any→ℕ≤length {xs = x ∷ xs} (here px) = z<s
any→ℕ≤length {xs = x ∷ xs} (there a) = s<s (any→ℕ≤length a)

-- TODO this should go into Prefix.Properties?

opaque
  unfolding Prefix
  at-prefix : {P : Pred A ℓ′} {xs : List A} {n : ℕ}
            → Prefix xs ys → n < length xs
            → At P ys n → At P xs n
  at-prefix {P} {xs} {n} (pr , e) n< ay =
    [ id
    , (λ where (l≤ , _) → absurd (<→≱ n< l≤))
    ]ᵤ (at-++-split {xs = xs} $ subst (λ q → At P q n) (e ⁻¹) ay)

-- is-nil?

Reflects-is-nil? : Reflects (xs ＝ []) (is-nil? xs)
Reflects-is-nil? {xs = []}     = ofʸ refl
Reflects-is-nil? {xs = x ∷ xs} = ofⁿ false!

Dec-is-nil? : (xs : List A) → Dec (xs ＝ [])
Dec-is-nil? xs .does  = is-nil? xs
Dec-is-nil? _  .proof = Reflects-is-nil?

-- !ᵐ

-- TODO reflects?

!ᵐ-≥ : ∀ {A : Type ℓ} {xs : List A} {n : ℕ}
     → length xs ≤ n
     → xs !ᵐ n ＝ nothing
!ᵐ-≥ {xs = []}                 n≥ = refl
!ᵐ-≥ {xs = x ∷ xs} {n = zero}  n≥ = false! n≥
!ᵐ-≥ {xs = x ∷ xs} {n = suc n} n≥ = !ᵐ-≥ {xs = xs} {n = n} (≤-peel n≥)

≥-!ᵐ : ∀ {A : Type ℓ} {xs : List A} {n : ℕ}
     → xs !ᵐ n ＝ nothing
     → length xs ≤ n
≥-!ᵐ {xs = []} {n = n} e = z≤
≥-!ᵐ {xs = x ∷ xs} {n = zero} e = false! e
≥-!ᵐ {xs = x ∷ xs} {n = suc n} e = s≤s (≥-!ᵐ e)

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

!ᵐ-++< : ∀ {A : Type ℓ} {xs ys : List A} {n : ℕ}
       → n < length xs
       → (xs ++ ys) !ᵐ n ＝ xs !ᵐ n
!ᵐ-++< {xs = []}                 n< = false! n<
!ᵐ-++< {xs = x ∷ xs} {n = zero}  n< = refl
!ᵐ-++< {xs = x ∷ xs} {n = suc n} n< = !ᵐ-++< {xs = xs} (<-peel n<)

!ᵐ-++≥ : ∀ {A : Type ℓ} {xs ys : List A} {n : ℕ}
       → length xs ≤ n
       → (xs ++ ys) !ᵐ n ＝ ys !ᵐ (n ∸ length xs)
!ᵐ-++≥ {xs = []}                 n≥ = refl
!ᵐ-++≥ {xs = x ∷ xs} {n = zero}  n≥ = false! n≥
!ᵐ-++≥ {xs = x ∷ xs} {n = suc n} n≥ = !ᵐ-++≥ {xs = xs} (≤-peel n≥)

!ᵐ-++2< : ∀ {A : Type ℓ} {xs ys zs : List A} {n : ℕ}
       → n < length xs
       → (xs ++ ys) !ᵐ n ＝ (xs ++ zs) !ᵐ n
!ᵐ-++2< {xs = []}                 n< = false! n<
!ᵐ-++2< {xs = x ∷ xs} {n = zero}  n< = refl
!ᵐ-++2< {xs = x ∷ xs} {n = suc n} n< = !ᵐ-++2< {xs = xs} (<-peel n<)

opaque
  unfolding Prefix
  !ᵐ-prefix< : {A : 𝒰 ℓ} {xs ys : List A} {n : ℕ}
             → Prefix xs ys → n < length xs
             → ys !ᵐ n ＝ xs !ᵐ n
  !ᵐ-prefix< {n} (ts , e) n< = ap (_!ᵐ n) (e ⁻¹) ∙ !ᵐ-++< n<

At→Σ∈ₘ : {A : 𝒰 ℓ} {P : Pred A ℓ′} {xs : List A} {n : ℕ}
       → At P xs n
       → Σ[ x ꞉ A ] (x ∈ (xs !ᵐ n)) × P x
At→Σ∈ₘ {xs = x ∷ xs} (ahere px) = x , here refl , px
At→Σ∈ₘ {xs = x ∷ xs} (athere a) = At→Σ∈ₘ a

∈ₘ→At : {A : 𝒰 ℓ} {P : Pred A ℓ′} {xs : List A} {n : ℕ}
      → {z : A} → z ∈ (xs !ᵐ n) → P z
      → At P xs n
∈ₘ→At {P} {xs = x ∷ xs} {n = zero}  {z} (here e) pz = ahere (subst P e pz)
∈ₘ→At     {xs = x ∷ xs} {n = suc n} {z}  z∈      pz = athere (∈ₘ→At z∈ pz)

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

length>0→snoc : {A : 𝒰 ℓ} {xs : List A}
              → 0 < length xs → Σ[ ys ꞉ List A ] Σ[ y ꞉ A ] (xs ＝ ys ∷r y)
length>0→snoc {A} {xs} =
  snoc-elim
    (λ q → 0 < length q
         → Σ[ ys ꞉ List A ] Σ[ y ꞉ A ] (q ＝ ys ∷r y))
    false!
    (λ ys y _ _ → ys , y , refl)
    xs

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

at-∷r-init : {P : Pred A ℓ′} {xs : List A} {x : A} {n : ℕ}
           → At P xs n → At P (xs ∷r x) n
at-∷r-init {P} {xs} {n} pxs =
  subst (λ q → At P q n) (snoc-append xs ⁻¹) (at-++-l pxs)

at-∷r-last : {P : Pred A ℓ′} {xs : List A} {x : A}
           → P x → At P (xs ∷r x) (length xs)
at-∷r-last {P} {xs} {x} px =
  subst (λ q → At P (xs ∷r x) q) (+-zero-r (length xs)) $
  subst (λ q → At P q (length xs + 0)) (snoc-append xs ⁻¹)  $
  at-++-r {xs = xs} (ahere px)

at-∷r-split : {P : Pred A ℓ′} {xs : List A} {x : A} {n : ℕ}
            → At P (xs ∷r x) n → At P xs n ⊎ (n ＝ length xs) × P x
at-∷r-split {P} {xs} {n} a =
  map-r
    (λ where (le , a') →
               [ (λ where (px , eq) → ≤-antisym (∸=0≃≤ .fst eq) le , px)
               , (λ a'' → absurd (¬at-[] a''))
               ]ᵤ (at-uncons a'))
    (at-++-split {xs = xs} (subst (λ q → At P q n) (snoc-append xs) a))

any-∷r-split : {P : Pred A ℓ′} {x : A} {xs : List A}
             → Any P (xs ∷r x) → Any P xs ⊎ P x
any-∷r-split {P} {xs} pxs =
  map-r (any-¬there false!) (any-split (subst (λ q → Any P q) (snoc-append xs) pxs))

any-¬last : {P : Pred A ℓ′} {x : A} {xs : List A}
          → ¬ P x → Any P (xs ∷r x) → Any P xs
any-¬last {P} {xs} nx pxs =
  [ id , (λ a → absurd (nx a)) ]ᵤ (any-∷r-split pxs)

¬any-∷r : {P : Pred A ℓ′} {x : A} {xs : List A}
       → ¬ Any P xs → ¬ P x → ¬ Any P (xs ∷r x)
¬any-∷r nxs nx = contra (any-¬last nx) nxs

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

snoc-!ᵐ< : ∀ {A : Type ℓ} {xs : List A} {n : ℕ} {x : A}
         → n < length xs
         → (xs ∷r x) !ᵐ n ＝ xs !ᵐ n
snoc-!ᵐ< {xs} {n} n< = ap (_!ᵐ n) (snoc-append xs) ∙ !ᵐ-++< n<

snoc-!ᵐ= : ∀ {A : Type ℓ} {xs : List A} {n : ℕ} {x : A}
         → n ＝ length xs
         → (xs ∷r x) !ᵐ n ＝ just x
snoc-!ᵐ= {xs} {n} {x} e =
    ap (_!ᵐ n) (snoc-append xs)
  ∙ !ᵐ-++≥ {xs = xs} (=→≤ (e ⁻¹))
  ∙ ap ((x ∷ []) !ᵐ_) (≤→∸=0 (=→≤ e))

-- reverse

reverse-++ : ∀ {xs ys : List A}
           → reverse (xs ++ ys) ＝ reverse ys ++ reverse xs
reverse-++ {xs = []}     {ys} = ++-id-r (reverse ys) ⁻¹
reverse-++ {xs = x ∷ xs} {ys} =
    ap (_++ x ∷ []) (reverse-++ {xs = xs})
  ∙ ++-assoc (reverse ys) (reverse xs) (x ∷ [])

reverse-∷ : ∀ {xs : List A} {x}
          → reverse (x ∷ xs) ＝ reverse xs ∷r x
reverse-∷ {xs} = snoc-append (reverse xs) ⁻¹

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

reverse-⊆ : {xs : List A}
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

-- TODO move to Data.List.Operations.Properties.Map ?
foldl-map : {A : Type ℓ} {B : Type ℓ′}
            (z : C) (f : C → B → C) (h : A → B) (xs : List A)
          → fold-l f z (map h xs) ＝ fold-l (λ c → f c ∘ h) z xs
foldl-map z f h []       = refl
foldl-map z f h (x ∷ xs) = foldl-map (f z (h x)) f h xs

foldl-fusion : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
             {z : B} {f : B → A → B} {g : C → A → C} {h : B → C}
           → (∀ x y → h (f x y) ＝ g (h x) y)
           → (xs : List A)
           → h (fold-l f z xs) ＝ fold-l g (h z) xs
foldl-fusion                 eq []       = refl
foldl-fusion {z} {f} {g} {h} eq (x ∷ xs) =
    foldl-fusion {z = f z x} {g = g} eq xs
  ∙ ap (λ q → fold-l g q xs) (eq z x)

-- unsnoc

unsnoc-snoc : {xs : List A} {z w : A}
            → unsnoc z (xs ∷r w) ＝ (z ∷ xs , w)
unsnoc-snoc {xs = []}             =
  refl
unsnoc-snoc {xs = x ∷ xs} {z} {w} =
  let ih = unsnoc-snoc {xs = xs} {z = x} in
  ×-path (ap (λ q → z ∷ fst q) ih) (ap snd ih)

snoc-unsnoc : {z : A}
            → let (ys , y) = unsnoc z xs in
              ys ∷r y ＝ z ∷ xs
snoc-unsnoc {xs} {z} =
  snoc-elim
    (λ q → let (ys , y) = unsnoc z q in
           ys ∷r y ＝ z ∷ q)
    refl
    (λ ys y _ →
         let e = unsnoc-snoc {xs = ys} {z = z} {w = y} in
         ap² _∷r_ (ap fst e) (ap snd e))
    xs

unsnoc-map : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
             {z : A} {xs : List A} {f : A → B}
           → unsnoc (f z) (map f xs) ＝ bimap (map f) f (unsnoc z xs)
unsnoc-map     {xs = []}     = refl
unsnoc-map {z} {xs = x ∷ xs} {f} =
  let ih = unsnoc-map {z = x} {xs = xs} {f = f} in
  ×-path (ap (λ q → f z ∷ fst q) ih) (ap snd ih)

-- unconsᵐ / tailᵐ / unsnocᵐ

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

unsnocᵐ-map : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
              {xs : List A} {f : A → B}
            → unsnocᵐ (map f xs) ＝ map (bimap (map f) f) (unsnocᵐ xs)
unsnocᵐ-map {xs = []} = refl
unsnocᵐ-map {xs = x ∷ xs} = ap just unsnoc-map

unsnocᵐ-nothing : ∀ {A : Type ℓ} {xs : List A}
                → unsnocᵐ xs ＝ nothing
                → xs ＝ []
unsnocᵐ-nothing {xs = []}     e = refl
unsnocᵐ-nothing {xs = x ∷ xs} e = false! e

unsnocᵐ-∷r : ∀ {A : Type ℓ} {xs : List A}
           → xs ＝ Maybe.rec [] (_∷r_ $²_) (unsnocᵐ xs)
unsnocᵐ-∷r {xs = []}     = refl
unsnocᵐ-∷r {xs = x ∷ xs} = snoc-unsnoc ⁻¹

unsnocᵐ-len>0 : ∀ {A : Type ℓ} {xs : List A}
              → 0 < length xs
              → Anyᵐ (λ where (ys , y) → xs ＝ ys ∷r y) (unsnocᵐ xs)
unsnocᵐ-len>0 {xs = []}     prf = false! prf
unsnocᵐ-len>0 {xs = x ∷ xs} prf = here (snoc-unsnoc ⁻¹)

∷r-unsnocᵐ : ∀ {A : Type ℓ} {xs : List A} {z : A}
           → (xs , z) ∈ unsnocᵐ (xs ∷r z)
∷r-unsnocᵐ {xs} {z} =
  any-mapᵐ
    (λ where {x = (ys , y)} e →
                let (e1 , e2) = snoc-inj e in
                ×-path e1 e2)
    (unsnocᵐ-len>0 {xs = xs ∷r z} $
     <-≤-trans z<s (=→≤ (snoc-length xs ⁻¹)))

∷r-unsnocᵐ→ : ∀ {A : Type ℓ} {xs ys : List A} {z : A}
            → (ys , z) ∈ unsnocᵐ xs
            → xs ＝ ys ∷r z
∷r-unsnocᵐ→ m =
  unsnocᵐ-∷r ∙ ap (Maybe.rec [] (_$ₜ²_ _∷r_)) (∈→=just m)

-- concat

-- TODO split into sum + map length ?
length-concat : {xss : List (List A)}
              → length (concat xss) ＝ List.rec 0 (λ xs → length xs +_) xss
length-concat {xss} = rec-fusion ++-length xss

concat-++ : {xss yss : List (List A)}
          → concat (xss ++ yss) ＝ concat xss ++ concat yss
concat-++ {xss} {yss} =
    rec-++ _ _ xss yss
  ∙ rec-fusion (λ x y → ++-assoc x y _) xss ⁻¹

concat-∷r : {xss : List (List A)} {xs : List A}
          → concat (xss ∷r xs) ＝ concat xss ++ xs
concat-∷r {xss} {xs} =
    ap concat (snoc-append xss)
  ∙ concat-++ {xss = xss}
  ∙ ap (concat xss ++_) (++-id-r xs)

∈-concat : {x : A} {xss : List (List A)}
         → x ∈ concat xss
         → Σ[ xs ꞉ List A ] (xs ∈ xss × x ∈ xs)
∈-concat {xss = xs ∷ xss} x∈ =
  [ (λ x∈h → xs , here refl , x∈h)
  , (λ x∈t → let (xs , xs∈ , x∈xs) = ∈-concat x∈t in
             xs , there xs∈ , x∈xs)
  ]ᵤ (any-split {xs = xs} x∈)

concat-∈ : {x : A} {xss : List (List A)} {xs : List A}
         → xs ∈ xss → x ∈ xs
         → x ∈ concat xss
concat-∈ {x} {xss = zs ∷ xss} (here px)   x∈ = any-++-l (subst (x ∈_) px x∈ )
concat-∈     {xss = zs ∷ xss} (there xs∈) x∈ = any-++-r (concat-∈ xs∈ x∈)

ope-concat : {xss yss : List (List A)}
           → OPE xss yss
           → OPE (concat xss) (concat yss)
ope-concat  odone        = odone
ope-concat (otake e ope) = ope-++-ap (=→ope e) (ope-concat ope)
ope-concat (odrop ope)   = ope-concat ope ∙ ope-++-l

∥-concat : {xss : List (List A)}
         → ys ∥ concat xss → All (_∥_ ys) xss
∥-concat {xss = []} _ = []
∥-concat {xss = xs ∷ xss} d =
  let (dyx , d') = ∥-++←r {ys = xs} d in
  dyx ∷ ∥-concat d'

concat-∥ : {xss : List (List A)}
         → All (_∥_ ys) xss
         → ys ∥ concat xss
concat-∥ {xss = []}       []       = ∥-[]-r
concat-∥ {xss = xs ∷ xss} (dx ∷ a) = ∥-++→r dx (concat-∥ a)

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

pairwise→filter : {R : A → A → 𝒰 ℓ′} {xs : List A} {p : A → Bool}
                → Pairwise R xs → Pairwise R (filter p xs)
pairwise→filter {xs = []}          []ᵖ       = []ᵖ
pairwise→filter {xs = x ∷ xs} {p} (ax ∷ᵖ px) with p x
... | true = all→filter ax ∷ᵖ pairwise→filter px
... | false = pairwise→filter px

all-filter : {p : A → Bool} {xs : List A}
           → ⌞ all p (filter p xs) ⌟
all-filter {p} {xs = []}     = oh
all-filter {p} {xs = x ∷ xs} =
  Bool.elim
    {P = λ q → p x ＝ q → ⌞ all p (if q then x ∷ filter p xs else filter p xs) ⌟}
    (λ e → (so≃is-true ⁻¹ $ e) × all-filter {xs = xs})
    (λ _ → all-filter {xs = xs})
    (p x) refl

none-filter : {p : A → Bool} {xs : List A}
            → filter p xs ＝ []
            → ⌞ not (any p xs) ⌟
none-filter {p} {xs = []}     _ = oh
none-filter {p} {xs = x ∷ xs}   =
  Bool.elim
    {P = λ q → (if q then x ∷ filter p xs else filter p xs) ＝ [] → ⌞ not (q or any p xs) ⌟}
    false!
    (none-filter {xs = xs})
    (p x)

filter-all : {p : A → Bool} {xs : List A}
           → ⌞ all p xs ⌟ → filter p xs ＝ xs
filter-all     {xs = []}     _ = refl
filter-all {p} {xs = x ∷ xs} s =
  let pax = and-so-≃ {x = p x} $ s in
  if-true (pax .fst) ∙ ap (x ∷_) (filter-all (pax .snd))

filter-none : {p : A → Bool} {xs : List A}
            → ⌞ not (any p xs) ⌟
            → filter p xs ＝ []
filter-none     {xs = []}     na = refl
filter-none {p} {xs = x ∷ xs} na =
  let nax = and-so-≃ {x = not (p x)} $ subst So (not-or (p x) _) na in
  if-false (nax .fst) ∙ filter-none {xs = xs} (nax .snd)

Reflects-filter-all : {p : A → Bool} {xs : List A}
                    → Reflects (filter p xs ＝ xs) (all p xs)
Reflects-filter-all {p} {xs} =
  Reflects.dmap filter-all
    (contra λ e → subst (So ∘ all p) e (all-filter {xs = xs}))
    Reflects-So

Reflects-filter-none : {p : A → Bool} {xs : List A}
                    → Reflects (filter p xs ＝ []) (not (any p xs))
Reflects-filter-none {p} {xs} =
  Reflects.dmap (filter-none {xs = xs})
    (contra $ none-filter {xs = xs})
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

⊆-filter : ∀ {p : A → Bool} {xs ys}
         → xs ⊆ ys → filter p xs ⊆ filter p ys
⊆-filter {xs} {ys} sub {x} x∈ =
  let (px , x∈') = filter-∈ {xs = xs} x∈ in
  ∈-filter {xs = ys} px (sub x∈')

ope-filter : ∀ {p : A → Bool} {xs ys}
           → OPE xs ys → OPE (filter p xs) (filter p ys)
ope-filter      odone          = odone
ope-filter {p} (otake {x} {y} exy oxy) with p x | recall p x
ope-filter {p} (otake {x} {y} exy oxy) | false | ⟪ eq ⟫ =
  ope-trans
    (ope-filter oxy)
    (=→ope (if-false (not-so (¬so≃is-false ⁻¹ $ ap p exy ⁻¹ ∙ eq)) ⁻¹))
ope-filter {p} (otake {x} {y} exy oxy) | true | ⟪ eq ⟫ =
  ope-trans
    (otake exy (ope-filter oxy))
    (=→ope (if-true (so≃is-true ⁻¹ $ ap p exy ⁻¹ ∙ eq) ⁻¹))
ope-filter {p} (odrop {y} oxy) with p y | recall p y
ope-filter {p} (odrop {y} oxy) | false | ⟪ eq ⟫ =
  ope-filter oxy
ope-filter {p} (odrop {y} oxy) | true | ⟪ eq ⟫ =
  odrop (ope-filter oxy)

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

filter-map : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {xs : List A} {p : B → Bool} {f : A → B}
           → filter p (map f xs) ＝ map f (filter (p ∘ f) xs)
filter-map {xs = []}     = refl
filter-map {xs = x ∷ xs} {p} {f} with p (f x)
... | true = ap (f x ∷_) (filter-map {xs = xs})
... | false = filter-map {xs = xs}

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

count-∷r : ∀ (p : A → Bool) xs x
         → count p (xs ∷r x) ＝ count p xs + bit (p x)
count-∷r p xs x =
    ap (count p) (snoc-append xs)
  ∙ count-++ p xs (x ∷ [])
  ∙ ap (count p xs +_) (+-zero-r _)

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
all→count p xs px =
    length-filter p xs ⁻¹
  ∙ ap length
       (filter-all $
        true→so! ⦃ Reflects-all-bool ⦄ px)

none→count : ∀ (p : A → Bool) xs
           → All (So ∘ not ∘ p) xs → count p xs ＝ 0
none→count p xs na =
    length-filter p xs ⁻¹
  ∙ ap length
       (filter-none {xs = xs} $
        subst So (not-any? {xs = xs} ⁻¹) $
        true→so! ⦃ Reflects-all-bool ⦄ na)

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

count-complement : ∀ p (xs : List A)
                 → count p xs + count (not ∘ p) xs ＝ length xs
count-complement p xs =
    count-union-inter p (not ∘ p) xs ⁻¹
  ∙ ap² _+_ (all→count (λ z → p z or not (p z)) xs
               (all-trivial λ x → so≃is-true ⁻¹ $ or-compl (p x)))
            (none→count (λ z → p z and not (p z)) xs
               (all-trivial λ x → not-so-≃ ⁻¹ $ ¬so≃is-false ⁻¹ $ and-compl (p x)))
  ∙ +-zero-r (length xs)

count-none : {p : A → Bool} {xs : List A}
            → ⌞ not (any p xs) ⌟
            → count p xs ＝ 0
count-none {p} {xs} np =
  length-filter p xs ⁻¹ ∙ ap length (filter-none {xs = xs} np)

count-false : (xs : List A)
            → count (λ _ → false) xs ＝ 0
count-false xs =
  length-filter (λ _ → false) xs ⁻¹ ∙ ap length (filter-false xs)

count-true : (xs : List A)
           → count (λ _ → true) xs ＝ length xs
count-true xs = length-filter (λ _ → true) xs ⁻¹ ∙ ap length (filter-true xs)

count-map : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {xs : List A} {p : B → Bool} {f : A → B}
          → count p (map f xs) ＝ count (p ∘ f) xs
count-map {xs} {p} {f} = rec-map 0 (λ x n → bit (p x) + n) f xs

ope-count : ∀ {p : A → Bool} {xs ys}
          → OPE xs ys → count p xs ≤ count p ys
ope-count {p} {xs} {ys} ope =
  =→≤ (length-filter p xs ⁻¹) ∙ ope-length (ope-filter ope) ∙ =→≤ (length-filter p ys)

-- TODO All?
count-≤-implies : ∀ {p q : A → Bool} {xs}
                → (∀ {x} → x ∈ xs → ⌞ p x implies q x ⌟)
                → count p xs ≤ count q xs
count-≤-implies {xs = []}     imp = refl
count-≤-implies {xs = x ∷ xs} imp =
  ≤-+
    (bit-implies _ _ (imp (here refl)))
    (count-≤-implies (imp ∘ there))

-- TODO All+Any?
-- TODO better proof
count-<-implies : {A : 𝒰 ℓ} {p q : A → Bool} {xs : List A}
                → (∀ {x} → x ∈ xs → ⌞ p x implies q x ⌟)
                → (Σ[ x ꞉ A ] x ∈ xs × ⌞ not (p x) ⌟ × ⌞ q x ⌟)
                → count p xs < count q xs
count-<-implies {p} {q} {xs = x ∷ xs} imp (z , here ez  , npz , qz) =
  <-≤-+
    (≤-<-trans (=→≤ (ap bit (ap p (ez ⁻¹) ∙ (¬so≃is-false $ so-not npz))))
       (<-≤-trans z<s
          (=→≤ (ap bit ((so≃is-true $ qz) ⁻¹ ∙ ap q ez)))))
    (count-≤-implies (imp ∘ there))
count-<-implies         {xs = x ∷ xs} imp (z , there z∈ , npz , qz) =
  ≤-<-+ (bit-implies _ _ (imp (here refl))) (count-<-implies (imp ∘ there) (z , z∈ , npz , qz))

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

opaque
  unfolding Prefix
  take-prefix : {n : ℕ} {xs : List A}
              → Prefix (take n xs) xs
  take-prefix {n} {xs} = drop n xs , split-take-drop n ⁻¹

-- map-maybe

map-maybe-∈-= : ∀ {ℓᵇ} {B : 𝒰 ℓᵇ} {xs : List A}
              → {f g : A → Maybe B}
              → (∀ {x} → x ∈ xs → f x ＝ g x)
              → map-maybe f xs ＝ map-maybe g xs
map-maybe-∈-= {xs = []}     e = refl
map-maybe-∈-= {xs = x ∷ xs} e =
  ap² (λ a b → Maybe.rec a (_∷ a) b) (map-maybe-∈-= (e ∘ there)) (e (here refl))

count-map-maybe : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {xs : List A} {p : B → Bool} {f : A → Maybe B}
                → count p (map-maybe f xs) ＝ count (Maybe.rec false p ∘ f) xs
count-map-maybe {xs = []}     {p} {f} = refl
count-map-maybe {xs = x ∷ xs} {p} {f} with f x
... | just z  = ap (bit (p z) +_) (count-map-maybe {xs = xs})
... | nothing = count-map-maybe {xs = xs}

-- take-while & drop-while

take-while-all : ∀ {A : 𝒰 ℓ} (p : A → Bool) xs
               → All (So ∘ p) (take-while p xs)
take-while-all p []       = []
take-while-all p (x ∷ xs) with p x | recall p x
... | false | ⟪ e ⟫ = []
... | true  | ⟪ e ⟫ = subst So (e ⁻¹) oh ∷ (take-while-all p xs)

take-while-++-l : ∀ {A : 𝒰 ℓ} {p : A → Bool} xs {ys}
                → All (So ∘ p) xs
                → take-while p (xs ++ ys) ＝ xs ++ take-while p ys
take-while-++-l []       []       = refl
take-while-++-l (x ∷ xs) (a ∷ as) = if-true a ∙ ap (x ∷_) (take-while-++-l xs as)

all-take-while : ∀ {A : 𝒰 ℓ} {p : A → Bool} xs
               → All (So ∘ p) xs
               → take-while p xs ＝ xs
all-take-while {p} xs a =
    ap (take-while p) (++-id-r xs ⁻¹)
  ∙ take-while-++-l xs {ys = []} a
  ∙ ++-id-r xs

take-while-prefix : ∀ {A : 𝒰 ℓ} {p : A → Bool} {xs}
                  → Prefix (take-while p xs) xs
take-while-prefix     {xs = []}     = []-prefix
take-while-prefix {p} {xs = x ∷ xs} with p x
... | false = []-prefix
... | true  = ∷-prefix refl (take-while-prefix {xs = xs})

eq-take-drop-while : ∀ {A : 𝒰 ℓ} (p : A → Bool) xs
                   → Any (So ∘ p) xs
                   → Σ[ x ꞉ A ] (  So (p x)
                                 × (xs ＝              take-while (not ∘ p) xs
                                          ++ x ∷ tail (drop-while (not ∘ p) xs)))
eq-take-drop-while p (x ∷ xs) a with p x | recall p x
... | true | ⟪ eq ⟫ =
    x , (so≃is-true ⁻¹ $ eq) , refl
... | false | ⟪ eq ⟫ =
  let (q , pq , e) = eq-take-drop-while p xs (any-¬here (¬so≃is-false ⁻¹ $ eq) a) in
  q , pq , ap (x ∷_) e

-- span
-- TODO duplication with above

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

span-++-r : ∀ {p : A → Bool} xs {ys}
          → All (So ∘ p) xs
          → span p (xs ++ ys) ＝ (xs ++ span p ys .fst , span p ys .snd)
span-++-r     []          []        = refl
span-++-r {p} (x ∷ xs) {ys} (px ∷ ax) =
  let ih = span-++-r xs {ys = ys} ax in
  if-true px ∙ ×-path (ap (λ q → x ∷ fst q) ih) (ap snd ih)

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

count-from-to-split : {m n p : ℕ}
                    → m ≤ p → p ≤ n
                    → count-from-to m n ＝ count-from-to m p ++ count-from-to p n
count-from-to-split     {n} {p = zero}  m≤p _   =
  ap (λ q → count-from-to q n) (≤0→=0 m≤p)
count-from-to-split {m} {n} {p = suc p} m≤p p≤n =
  [ (λ m< → let m≤ = ≤≃<suc ⁻¹ $ m< in
              count-from-to-split {n = n} m≤ (≤-ascend ∙ p≤n)
            ∙ ap (count-from-to m p ++_)
                 (count-from-to-suc-l {n = n} (<≃suc≤ $ p≤n))
            ∙ ++-assoc (count-from-to m p) _ _ ⁻¹
            ∙ ap (_++ count-from-to (1 + p) n)
                 (  snoc-append (count-from-to m p) ⁻¹
                  ∙ count-from-to-suc-r {m = m} m≤ ⁻¹))
  , (λ m= →   ap (_++ count-from-to m n) (count-from-to-idem {n = m} ⁻¹)
            ∙ ap (λ q → count-from-to m q ++ count-from-to q n) m=)
  ]ᵤ (≤→<⊎= m≤p)

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
  let (l , l∈ , le) = List.map-∈Σ suc k∈
      ih< = count-from-to-∈ l∈ .snd
    in
  z≤ , subst (_< suc n) (le ⁻¹) (s<s ih<)
count-from-to-∈ {m = suc m} {n = suc n} k∈ =
  let (l , l∈ , le) = List.map-∈Σ suc k∈
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
  there (List.∈-map suc (∈-count-from-to {m = 0} {n = n} {k = k} z≤ (<-peel k<n)))
∈-count-from-to {m = suc m} {n = suc n} {k = zero}  m≤k _   = false! m≤k
∈-count-from-to {m = suc m} {n = suc n} {k = suc k} m≤k k<n =
  List.∈-map suc (∈-count-from-to {m = m} {n = n} {k = k} (≤-peel m≤k) (<-peel k<n))

-- TODO ≃

-- partition

partition-filter : {p : A → Bool} {xs : List A}
                 → partition p xs ＝ (filter p xs , filter (not ∘ p) xs)
partition-filter     {xs = []}     = refl
partition-filter {p} {xs = x ∷ xs} with p x
... | true  =
  let ih = ×-path-inv $ partition-filter {p = p} {xs = xs} in
  ×-path (ap (x ∷_) (ih .fst)) (ih .snd)
... | false =
  let ih = ×-path-inv $ partition-filter {p = p} {xs = xs} in
  ×-path (ih .fst) (ap (x ∷_) (ih .snd))
