{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Membership where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Path
open import Data.List.Base
open import Data.List.Instances.Map
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.Maybe.Base
open import Data.Maybe.Path using (just-inj)
open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

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
∈≃fibre {A} {x} s = ≅→≃ (make-iso to fro (make-inverses (fun-ext re) (fun-ext se)))
  where
  to : {xs : List A} → x ∈ xs → fibre (xs !ᶠ_) x
  to hx = any→fin hx , any→fin-!ᶠ hx ⁻¹
  fro : {xs : List A} → fibre (xs !ᶠ_) x → x ∈ xs
  fro {y ∷ xs} (mk-fin zero             , e) = here (e ⁻¹)
  fro {y ∷ xs} (mk-fin (suc ix) {bound} , e) = there (fro ((mk-fin ix {bound}) , e))
  re : {xs : List A} → (f : fibre (xs !ᶠ_) x) → to (fro f) ＝ f
  re {y ∷ xs} (mk-fin zero             , e) = refl
  re {y ∷ xs} (mk-fin (suc ix) {bound} , e) =
    Σ-prop-path (λ q → s ((y ∷ xs) !ᶠ q) x)
      (fin-ext (ap (suc ∘ Fin.index ∘ fst) (re {xs} (mk-fin ix {bound} , e))))
  se : {xs : List A} → (h : x ∈ xs) → fro (to h) ＝ h
  se {y ∷ xs} (here px) = refl
  se {y ∷ xs} (there h) = ap there (se h)

instance
  -- TODO duplication with Data.List.Operations.Discrete
  Dec-∈ₗ
    : {a : A} {xs : List A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈ xs)
  Dec-∈ₗ {xs = []} = no λ()
  Dec-∈ₗ {a} {xs = x ∷ xs} .does = (a =? x) or ⌊ Dec-∈ₗ {a = a} {xs = xs} ⌋
  Dec-∈ₗ {a} {xs = x ∷ xs} .proof =
    caseᵈ a ＝ x return (λ d → Reflects (a ∈ (x ∷ xs)) (⌊ d ⌋ or ⌊ Dec-∈ₗ {a = a} {xs = xs} ⌋)) of λ where
      (yes a=x) → ofʸ (here a=x)
      (no  a≠x) → case Dec-∈ₗ {a = a} {xs = xs} return (λ d → Reflects (a ∈ (x ∷ xs)) ⌊ d ⌋) of λ where
        (yes a∈xs) → ofʸ (there a∈xs)
        (no  a∉xs) → ofⁿ λ where
          (here  a=x)  → a≠x a=x
          (there a∈xs) → a∉xs a∈xs
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

∈-split : {A : 𝒰 ℓᵃ} {x : A} {xs : List A}
         → x ∈ xs → Σ[ ls ꞉ List A ] Σ[ rs ꞉ List A ] (xs ＝ ls ++ x ∷ rs)
∈-split {xs = x ∷ xs} (here e)   = [] ,  xs , ap (_∷ xs) (e ⁻¹)
∈-split {xs = x ∷ xs} (there hx) =
  let (ls , rs , e) = ∈-split hx in
  x ∷ ls , rs , ap (x ∷_) e

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
∀∈→All {xs = []} ax = []
∀∈→All {xs = x ∷ xs} ax = ax x (here refl) ∷ ∀∈→All λ y hy → ax y (there hy)

all-∈-map : ∀ {ℓ′} {P : Pred A ℓ} {Q : Pred A ℓ′}
            → (∀ {x} → x ∈ xs → P x → Q x)
            → All P xs → All Q xs
all-∈-map {xs = []}     f []       = []
all-∈-map {xs = x ∷ xs} f (p ∷ ps) = f (here refl) p ∷ all-∈-map (f ∘ there) ps

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
