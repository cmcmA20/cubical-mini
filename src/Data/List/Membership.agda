{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Membership where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Effect

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Unit.Base
open import Data.Empty.Base as ⊥
open import Data.Bool.Base
open import Data.Reflects.Base as Reflects
open import Data.Dec.Base as Dec
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Path
open import Data.Sum.Base
open import Data.List.Base
open import Data.List.Instances.Map
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.Maybe.Base
open import Data.Maybe.Path using (just-inj)

private variable
  ℓᵃ ℓ : Level
  A : Type ℓᵃ
  a x y : A
  xs : List A

_∈ₗ_ : ∀ {ℓᵃ} {A : Type ℓᵃ}
     → A → List A → Type ℓᵃ
x ∈ₗ xs = Any (x ＝_) xs

instance
  Membership-List : {A : Type ℓ} → Membership A (List A) ℓ
  Membership-List ._∈_ = _∈ₗ_

instance
  ∈ₗ-head : {xs : List A} → Reflects (x ∈ₗ (x ∷ xs)) true
  ∈ₗ-head = ofʸ (here refl)
  {-# OVERLAPPING ∈ₗ-head #-}

-- TODO can this be generalized to arbitrary hlevel?
∈≃fibre : {xs : List A} → is-set A → x ∈ xs ≃ fibre (xs !ᶠ_) x
∈≃fibre {A} {x} s = ≅→≃ (iso to (λ (n , p) → fro n p) (fun-ext λ (n , p) → re n p) (fun-ext se))
  where
  to : {xs : List A} → x ∈ xs → fibre (xs !ᶠ_) x
  to hx = any→fin hx , any→fin-!ᶠ hx ⁻¹
  fro : {xs : List A} (k : Fin (length xs)) (e : xs !ᶠ k ＝ x) → x ∈ xs
  fro {y ∷ xs} (mk-fin zero)     e = here (e ⁻¹)
  fro {y ∷ xs} (mk-fin (suc ix)) e = there (fro (mk-fin ix) e)
  re : {xs : List A} (k : Fin (length xs)) (e : xs !ᶠ k ＝ x) → to (fro k e) ＝ (k , e)
  re {y ∷ xs} (mk-fin zero)             e = refl
  re {y ∷ xs} (mk-fin (suc ix) {bound}) e =
    Σ-prop-path (λ q → s ((y ∷ xs) !ᶠ q) x)
      (fin-ext (ap (suc ∘ Fin.index ∘ fst) (re {xs} (mk-fin ix {bound}) e)))
  se : {xs : List A} → (h : x ∈ xs) → let (k , e) = to h in fro k e ＝ h
  se {y ∷ xs} (here px) = refl
  se {y ∷ xs} (there h) = ap there (se h)

has : ⦃ d : is-discrete A ⦄ → A → List A → Bool
has a = any (λ x → ⌊ a ≟ x ⌋)

Reflects-has : ⦃ d : is-discrete A ⦄ {x : A} {xs : List A}
             → Reflects (x ∈ xs) (has x xs)
Reflects-has ⦃ d ⦄ {x} = Reflects-any λ y → d {x} {y} .proof

instance
  Dec-∈ₗ
    : {a : A} {xs : List A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈ xs)
  Dec-∈ₗ {a} {xs} .does = has a xs
  Dec-∈ₗ          .proof = Reflects-has
  {-# OVERLAPPING Dec-∈ₗ #-}

  ∈ₗ-is-discrete
    : {a : A} {xs : List A}
    → ⦃ A-set : H-Level 2 A ⦄
    → is-discrete (a ∈ xs)
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = here p}  {here p′}  = yes (ap here prop!)
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = here p}  {there q}  = no false!
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = there q} {here p′}  = no false!
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = there q} {there q′} =
    case (∈ₗ-is-discrete {a = a} {xs = xs} {q} {q′}) of λ where
      (yes q=q′) → yes (ap there q=q′)
      (no  q≠q′) → no (contra there-inj q≠q′)
  {-# OVERLAPPING ∈ₗ-is-discrete #-}


here+there→∉!ₗ : a ＝ x → a ∈ xs → a ∉! (x ∷ xs)
here+there→∉!ₗ _   a∈xs (here  p , uniq) = here≠there $ uniq (there a∈xs)
here+there→∉!ₗ a=x _    (there q , uniq) = there≠here $ uniq (here a=x)

¬here+¬there!→∉!ₗ : a ≠ x → a ∉! xs → a ∉! (x ∷ xs)
¬here+¬there!→∉!ₗ a≠x _     (here  a=x  , _)    = a≠x a=x
¬here+¬there!→∉!ₗ _   a∉!xs (there a∈xs , uniq) = a∉!xs (a∈xs , there-inj ∘ uniq ∘ there)

here+¬there→∈!ₗ
  : {a x : A} {xs : List A} ⦃ A-set : H-Level 2 A ⦄
  → a ＝ x → a ∉ xs → a ∈! (x ∷ xs)
here+¬there→∈!ₗ a=x a∉xs = here a=x , λ where
  (here  _)    → ap here prop!
  (there a∈xs) → false! $ a∉xs a∈xs

¬here+there!→∈!ₗ : a ≠ x → a ∈! xs → a ∈! (x ∷ xs)
¬here+there!→∈!ₗ a≠x (a∈xs , uniq) = there a∈xs , λ where
  (here  a=x)   → false! $ a≠x a=x
  (there a∈xs′) → ap there (uniq a∈xs′)

instance
  Dec-∈!ₗ
    : {a : A} {xs : List A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈! xs)
  Dec-∈!ₗ {xs = []} = no λ ()
  Dec-∈!ₗ {a} {xs = x ∷ xs} =
    caseᵈ a ＝ x of λ where
      (yes a=x) → caseᵈ a ∈ xs of λ where
        (yes a∈xs) → no  (here+there→∉!ₗ  a=x a∈xs)
        (no  a∉xs) → yes (here+¬there→∈!ₗ a=x a∉xs)
      (no  a≠x) → case Dec-∈!ₗ {a = a} {xs} of λ where
        (yes a∈!xs) → yes (¬here+there!→∈!ₗ  a≠x a∈!xs)
        (no  a∉!xs) → no  (¬here+¬there!→∉!ₗ a≠x a∉!xs)
  {-# OVERLAPPING Dec-∈!ₗ #-}

∈ₗ→fin-almost-injective
  : {A : Type ℓᵃ} {a b : A} {xs : List A}
    (u : a ∈ xs) (v : b ∈ xs)
  → any→fin u ＝ any→fin v
  → a ＝ b
∈ₗ→fin-almost-injective {xs = x ∷ xs} (here eu) (here ev) _ = eu ∙ ev ⁻¹
∈ₗ→fin-almost-injective {xs = x ∷ xs} (here eu) (there v) r = false! r
∈ₗ→fin-almost-injective {xs = x ∷ xs} (there u) (here ev) r = false! r
∈ₗ→fin-almost-injective {xs = x ∷ xs} (there u) (there v) r = ∈ₗ→fin-almost-injective u v (fsuc-inj r)

∈!ₗ↪fin
  : {a : A} {xs : List A}
  → a ∈! xs ↪ Fin (length xs)
∈!ₗ↪fin .fst = any→fin ∘ fst
∈!ₗ↪fin .snd _ _ _ = prop!

instance
  ∈!ₗ-is-discrete
    : {a : A} {xs : List A}
    → is-discrete (a ∈! xs)
  ∈!ₗ-is-discrete = ↪→is-discrete! ∈!ₗ↪fin
  {-# OVERLAPPABLE ∈!ₗ-is-discrete #-}

∈ₗ→fin-respects-∈!ₗ
  : {A : Type ℓᵃ} {a b : A} {xs : List A}
    (u : a ∈ xs) → is-central u
  → (v : b ∈ xs) → is-central v
  → a ＝ b
  → any→fin u ＝ any→fin v
∈ₗ→fin-respects-∈!ₗ {xs = x ∷ xs} (here  p) _ (here  p′) _ _ = refl
∈ₗ→fin-respects-∈!ₗ {xs = x ∷ xs} (here  p) _ (there q)  v r =
  false! $ v $ here $ r ⁻¹ ∙ p
∈ₗ→fin-respects-∈!ₗ {xs = x ∷ xs} (there q) u (here  p)  _ r =
  false! $ u $ here $ r ∙ p
∈ₗ→fin-respects-∈!ₗ {xs = x ∷ xs} (there q) u (there q′) v r =
  ap fsuc (∈ₗ→fin-respects-∈!ₗ q (there-inj ∘ u ∘ there) q′ (there-inj ∘ v ∘ there) r)

∈-map : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xs : List A}
      → (f : A → B) → x ∈ xs → f x ∈ map f xs
∈-map {xs = x ∷ xs} f (here e)   = here (ap f e)
∈-map {xs = x ∷ xs} f (there hx) = there (∈-map f hx)

map-∈ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xs : List A}
      → (f : A → B) → Injective f
      → f x ∈ map f xs → x ∈ xs
map-∈ {xs = x ∷ xs} f inj (here e)   = here (inj e)
map-∈ {xs = x ∷ xs} f inj (there fx) = there (map-∈ f inj fx)

∉-map : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xs : List A} {f : A → B}
      → Injective f
      → x ∉ xs → f x ∉ map f xs
∉-map fi = contra (map-∈ _ fi)

map-∈-= : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {xs : List A}
       → {f g : A → B}
       → (∀ {x} → x ∈ xs → f x ＝ g x)
       → map f xs ＝ map g xs
map-∈-= {xs = []}     e = refl
map-∈-= {xs = x ∷ xs} e = ap² {C = λ _ _ → List _} _∷_ (e (here refl)) (map-∈-= (e ∘ there))

{-
map-∈-in : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {z : A} {xs : List A}
       → (f : A → B)
       → (∀ {x y} → y ∈ xs → f x ＝ f y → x ＝ y)
       → f z ∈ map f xs → z ∈ xs
map-∈-in {xs = x ∷ xs} f inj (here e)  = here (inj (here refl) e)
map-∈-in {xs = x ∷ xs} f inj (there fx) = there (map-∈-in f (λ {x} {y} y∈ e → inj (there y∈) e) fx)
-}

map-∈Σ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {y : B} {xs : List A}
       → (f : A → B)
       → y ∈ map f xs → Σ[ x ꞉ A ] ((x ∈ xs) × (y ＝ f x))
map-∈Σ {xs = x ∷ xs} f (here e) = x , here refl , e
map-∈Σ {xs = x ∷ xs} f (there y∈) =
  let (x , x∈ , xe) = map-∈Σ f y∈ in
  x , there x∈ , xe

map-⊆ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {xs ys : List A}
      → (f : A → B)
      → xs ⊆ ys
      → map f xs ⊆ map f ys
map-⊆ {ys} f sub {x} x∈m =
  let (z , z∈ , xe) = map-∈Σ f x∈m in
  subst (_∈ map f ys) (xe ⁻¹) $
  ∈-map f $
  sub z∈

⊆-map : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {xs ys : List A}
      → (f : A → B) → Injective f
      → map f xs ⊆ map f ys
      → xs ⊆ ys
⊆-map {ys} f fi sub {x} x∈xs =
  map-∈ f fi $ sub $ ∈-map f x∈xs

∈-split : {A : 𝒰 ℓᵃ} {x : A} {xs : List A}
         → x ∈ xs → Σ[ ls ꞉ List A ] Σ[ rs ꞉ List A ] (xs ＝ ls ++ x ∷ rs)
∈-split {xs = x ∷ xs} (here e)   = [] ,  xs , ap (_∷ xs) (e ⁻¹)
∈-split {xs = x ∷ xs} (there hx) =
  let (ls , rs , e) = ∈-split hx in
  x ∷ ls , rs , ap (x ∷_) e

map-with-∈ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
           → (xs : List A)
           → ((a : A) → a ∈ xs → B)
           → List B
map-with-∈ []       f = []
map-with-∈ (x ∷ xs) f = f x (here refl) ∷ map-with-∈ xs (λ a → f a ∘ there)

rec-with-∈ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
           → B
           → (xs : List A)
           → ((a : A) → a ∈ xs → B → B)
           → B
rec-with-∈ z []       f = z
rec-with-∈ z (x ∷ xs) f = f x (here refl) (rec-with-∈ z xs λ a → f a ∘ there)

-- interaction with any/all

Any→Σ∈ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs : List A}
       → Any P xs
       → Σ[ x ꞉ A ] x ∈ xs × P x
Any→Σ∈ {xs = x ∷ xs} (here px) = x , here refl , px
Any→Σ∈ {xs = x ∷ xs} (there a)     =
  let (x , h , p) = Any→Σ∈ a in
  x , there h , p

∈→Any : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs : List A} {x : A}
       → x ∈ xs → P x
       → Any P xs
∈→Any {P} {xs = y ∷ xs} (here e)   px = here (subst P e px)
∈→Any     {xs = y ∷ xs} (there hx) px = there (∈→Any hx px)

All→∀∈ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs : List A}
        → All P xs
        → (x : A) → x ∈ xs → P x
All→∀∈ {P} {xs = y ∷ xs} (px ∷ pxs) x (here e)   = subst P (e ⁻¹) px
All→∀∈     {xs = y ∷ xs} (px ∷ pxs) x (there hx) = All→∀∈ pxs x hx

∀∈→All : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs : List A}
        → ((x : A) → x ∈ xs → P x)
        → All P xs
∀∈→All {xs = []}     ax = []
∀∈→All {xs = x ∷ xs} ax = ax x (here refl) ∷ ∀∈→All λ y hy → ax y (there hy)

¬Any→All¬ : {xs : List A} {P : A → 𝒰 ℓ}
          → ¬ Any P xs → All (λ x → ¬ (P x)) xs
¬Any→All¬ nan = ∀∈→All λ x x∈ → nan ∘ ∈→Any x∈

All¬→¬Any : {xs : List A} {P : A → 𝒰 ℓ}
          → All (λ x → ¬ (P x)) xs → ¬ Any P xs 
All¬→¬Any al an =
  let (x , x∈ , px) = Any→Σ∈ an in
  All→∀∈ al x x∈ px

Any¬→¬All : {xs : List A} {P : A → 𝒰 ℓ}
          → Any (λ x → ¬ (P x)) xs → ¬ All P xs
Any¬→¬All an al =
  let (x , x∈ , px) = Any→Σ∈ an in
  px $ All→∀∈ al x x∈ 

all-⊆ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs ys : List A}
       → xs ⊆ ys → All P ys → All P xs
all-⊆ xsy ay = ∀∈→All λ x → All→∀∈ ay x ∘ xsy

all-∈-map : ∀ {ℓ′} {P : Pred A ℓ} {Q : Pred A ℓ′}
            → (∀ {x} → x ∈ xs → P x → Q x)
            → All P xs → All Q xs
all-∈-map {xs = []}     f []       = []
all-∈-map {xs = x ∷ xs} f (p ∷ ps) = f (here refl) p ∷ all-∈-map (f ∘ there) ps

any-⊆ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs ys : List A}
       → xs ⊆ ys → Any P xs → Any P ys
any-⊆ xsy ax =
  let (x , x∈ , px) = Any→Σ∈ ax in
  ∈→Any (xsy x∈) px

-- uniqueness

[]-unique : is-unique (the (List A) [])
[]-unique x h1 = false! h1

∷→unique : is-unique (x ∷ xs)
         → x ∉ xs × is-unique xs
∷→unique {x} u =
    (λ hx → false! (u x (here refl) (there hx)))
  , (λ y h1 h2 → there-inj (u y (there h1) (there h2)))

unique→∷ : {x : A}
         → is-set A
         → x ∉ xs → is-unique xs
         → is-unique (x ∷ xs)
unique→∷ {x}               s nx u z (here e1)  (here e2)  = ap here (s z x e1 e2)
unique→∷     {xs}          s nx u z (here e1)  (there h2) = ⊥.rec (nx (subst (_∈ₗ xs) e1 h2))
unique→∷     {xs}          s nx u z (there h1) (here e2)  = ⊥.rec (nx (subst (_∈ₗ xs) e2 h1))
unique→∷     {xs = y ∷ xs} s nx u z (there h1) (there h2) =
  let (nx , u′) = ∷→unique u in
  ap there (unique→∷ s nx u′ z h1 h2)

-- set-equivalence

≈-∷ : {x : A} {xs ys : List A}
    → xs ≈ ys
    → (x ∷ xs) ≈ (x ∷ ys)
≈-∷ (xy , yx) =
    [ here , there ∘ xy ]ᵤ ∘ any-uncons
  , [ here , there ∘ yx ]ᵤ ∘ any-uncons

-- disjointness
-- TODO move to Notation.Membership

_∥_ : List A → List A → Type (level-of-type A)
_∥_ {A} xs ys = ∀[ a ꞉ A ] (a ∈ xs → a ∈ ys → ⊥)

∥-comm : {xs ys : List A} → xs ∥ ys → ys ∥ xs
∥-comm dxy hy hx = dxy hx hy

∥-[]-l : {xs : List A} → [] ∥ xs
∥-[]-l = false!

∥-[]-r : {xs : List A} → xs ∥ []
∥-[]-r _ = false!

∥-∷→l : ∀ {x} {xs ys : List A} → x ∉ ys → xs ∥ ys → (x ∷ xs) ∥ ys
∥-∷→l {ys} ny dxy (here e)   hy = ny (subst (_∈ ys) e hy)
∥-∷→l      ny dxy (there hx) hy = dxy hx hy

∥-∷←l : ∀ {x} {xs ys : List A} → (x ∷ xs) ∥ ys → x ∉ ys × xs ∥ ys
∥-∷←l d = d (here refl) , d ∘ there

∥-∷→r : ∀ {y} {xs ys : List A} → y ∉ xs → xs ∥ ys → xs ∥ (y ∷ ys)
∥-∷→r nx = ∥-comm ∘ ∥-∷→l nx ∘ ∥-comm

map-∥ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
          {xs ys : List A} {f : A → B}
      → map f xs ∥ map f ys
      → xs ∥ ys
map-∥ {f} d xm ym =
  d (∈-map f xm) (∈-map f ym)

∥-map : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
          {xs ys : List A} {f : A → B}
      → Injective f
      → xs ∥ ys → map f xs ∥ map f ys
∥-map {ys} {f} inj d xm ym =
  let (a , am , xe) = map-∈Σ f xm
      (b , bm , ye) = map-∈Σ f ym
    in
  d am (subst (_∈ ys) (inj (ye ⁻¹ ∙ xe)) bm)
