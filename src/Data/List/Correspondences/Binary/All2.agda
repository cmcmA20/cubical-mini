{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.All2 where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Empty.Base
open import Data.Empty.Properties as ⊥p
open import Data.Unit.Base
open import Data.Unit.Properties
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.List.Base
open import Data.List.Operations
open import Data.Dec as Dec

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ¹ ℓ² ℓ³ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  P Q R : A → B → 𝒰 ℓ¹
  x : A
  y : B
  @0 xs : List A
  @0 ys : List B

data All2 {ℓᵃ ℓᵇ ℓ¹} {A : Type ℓᵃ} {B : Type ℓᵇ}
          (R : A → B → 𝒰 ℓ¹) : @0 List A → @0 List B → Type (ℓᵃ ⊔ ℓᵇ ⊔ ℓ¹) where
  []  : All2 R [] []
  _∷_ : R x y → All2 R xs ys → All2 R (x ∷ xs) (y ∷ ys)

module _ {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {R : A → B → 𝒰 ℓ¹}
         ⦃ ep : {a : A} {b : B} → Extensional (R a b) ℓ¹ ⦄ where
  Code-All2 : {xs : List A} {ys : List B} (p q : All2 R xs ys) → 𝒰 ℓ¹
  Code-All2 {xs = []}     {ys = []}     []       []       = Lift _ ⊤
  Code-All2 {xs = x ∷ xs} {ys = y ∷ ys} (px ∷ p) (qx ∷ q) = ep .Pathᵉ px qx × Code-All2 p q

  code-all2-refl : {xs : List A} {ys : List B} (p : All2 R xs ys) → Code-All2 p p
  code-all2-refl {xs = []}     {ys = []}     []       = lift tt
  code-all2-refl {xs = x ∷ xs} {ys = y ∷ ys} (px ∷ p) = ep .reflᵉ px , code-all2-refl p

  decode-All2 : {xs : List A} {ys : List B} {p q : All2 R xs ys} (c : Code-All2 p q) → p ＝ q
  decode-All2 {xs = []}     {ys = []}     {p = []}     {q = []}      _       = refl
  decode-All2 {xs = x ∷ xs} {ys = y ∷ ys} {p = px ∷ p} {q = qx ∷ q} (cx , c) =
    ap² {C = λ _ _ → All2 R (x ∷ xs) (y ∷ ys)} _∷_ (ep .idsᵉ .to-path cx) (decode-All2 c)

  decode-all2-refl : {xs : List A} {ys : List B} {p q : All2 R xs ys} (c : Code-All2 p q)
                  → code-all2-refl p ＝[ ap (Code-All2 p) (decode-All2 c) ]＝ c
  decode-all2-refl {xs = []}     {ys = []}     {p = []}     {q = []}     (lift tt) = refl
  decode-all2-refl {xs = x ∷ xs} {ys = y ∷ ys} {p = px ∷ p} {q = qx ∷ q} (cx , c)  =
    ep .idsᵉ .to-path-over cx ,ₚ decode-all2-refl c

  Extensional-All2 : {xs : List A} {ys : List B} → Extensional (All2 R xs ys) ℓ¹
  Extensional-All2 .Pathᵉ              = Code-All2
  Extensional-All2 .reflᵉ              = code-all2-refl
  Extensional-All2 .idsᵉ .to-path      = decode-All2
  Extensional-All2 .idsᵉ .to-path-over = decode-all2-refl

opaque
  code-All2-is-of-hlevel
    : ∀ {n} {xs : List A} {ys : List B} {u v : All2 R xs ys}
    → (∀ x y → is-of-hlevel (suc n) (R x y))
    → is-of-hlevel n (Code-All2 u v)
  code-All2-is-of-hlevel {n} {xs = []}     {ys = []}     {u = []}     {v = []}     hl = hlevel n
  code-All2-is-of-hlevel {n} {xs = x ∷ xs} {ys = y ∷ ys} {u = ux ∷ u} {v = vx ∷ v} hl =
    ×-is-of-hlevel n (path-is-of-hlevel n (hl x y) ux vx) (code-All2-is-of-hlevel hl)

-- All2 cannot be made contractible because the lists might not match

All2-is-of-hlevel
  : (n : HLevel) {xs : List A} {ys : List B}
  → (∀ x y → is-of-hlevel (suc n) (R x y))
  → is-of-hlevel (suc n) (All2 R xs ys)
All2-is-of-hlevel n hl =
  identity-system→is-of-hlevel n (Extensional-All2 .idsᵉ) (λ x y → code-All2-is-of-hlevel hl)

instance opaque
  H-Level-All2 : ∀ {n} {xs : List A} {ys : List B} → ⦃ n ≥ʰ 1 ⦄ → ⦃ A-hl : ∀ {x y} → H-Level n (R x y) ⦄ → H-Level n (All2 R xs ys)
  H-Level-All2 {n} ⦃ s≤ʰs _ ⦄ .H-Level.has-of-hlevel = All2-is-of-hlevel _ (λ x y → hlevel n)
  {-# OVERLAPPING H-Level-All2 #-}

all2-++ : {@0 as xs : List A} → {@0 bs ys : List B}
        → All2 R as bs → All2 R xs ys → All2 R (as ++ xs) (bs ++ ys)
all2-++ []        rxy = rxy
all2-++ (r ∷ rab) rxy = r ∷ all2-++ rab rxy

all2-split : {as : List A} {@0 xs : List A} {bs : List B} {@0 ys : List B}
           → length as ＝ length bs
           → All2 R (as ++ xs) (bs ++ ys) → All2 R as bs × All2 R xs ys
all2-split {as = []}     {bs = []}     _  rs      = [] , rs
all2-split {as = []}     {bs = b ∷ bs} e  rs      = absurd (zero≠suc e)
all2-split {as = a ∷ as} {bs = []}     e  rs      = absurd (suc≠zero e)
all2-split {as = a ∷ as} {bs = x ∷ bs} e (r ∷ rs) =
  let (rab , rxy) = all2-split (suc-inj e) rs in (r ∷ rab) , rxy

all2-map : {@0 xs : List A} {@0 ys : List B}
         → ({@0 x : A} {@0 y : B} → R x y → Q x y)
         → All2 R xs ys → All2 Q xs ys
all2-map     f []       = []
all2-map {R} f (r ∷ rs) = f r ∷ all2-map {R = R} f rs

all2-replicate-l : {x : A} {ys : List B}
                 → (∀ y → R x y)
                 → All2 R (replicate (length ys) x) ys
all2-replicate-l {ys = []}     h = []
all2-replicate-l {ys = y ∷ ys} h = h y ∷ all2-replicate-l h

all2-replicate-r : {xs : List A} {y : B}
                 → (∀ x → R x y)
                 → All2 R xs (replicate (length xs) y)
all2-replicate-r {xs = []}     h = []
all2-replicate-r {xs = x ∷ xs} h = h x ∷ all2-replicate-r h

all2-refl : {as : List A} {P : A → A → 𝒰 ℓ¹}
          → (∀ a → P a a)
          → All2 P as as
all2-refl {as = []}     pr = []
all2-refl {as = a ∷ as} pr = pr a ∷ all2-refl pr

all2-antisym : {as bs : List A}
               {P : A → A → 𝒰 ℓ¹}
             → (∀ a b → P a b → P b a → a ＝ b)
             → All2 P as bs → All2 P bs as → as ＝ bs
all2-antisym     {as = []}     {bs = []}     pa []        []          = refl
all2-antisym {A} {as = a ∷ as} {bs = b ∷ bs} pa (ab ∷ abs) (ba ∷ bas) =
  ap² {C = λ _ _ → List A} _∷_ (pa a b ab ba) (all2-antisym pa abs bas)

-- monotype version
all2-trans : {as bs cs : List A}
             {P : A → A → 𝒰 ℓ¹}
           → (∀ a b c → P a b → P b c → P a c)
           → All2 P as bs → All2 P bs cs → All2 P as cs
all2-trans {as = []}     {bs = .[]}    {cs = .[]}    pt  []        []         = []
all2-trans {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} pt (ab ∷ abs) (bc ∷ bcs) = pt a b c ab bc ∷ all2-trans pt abs bcs

all2-is-of-size : {P : A → B → 𝒰 ℓ¹} {as : List A} {bs : List B}
                → (∀ a b → is-of-size ℓ² (P a b))
                → is-of-size ℓ² (All2 P as bs)
all2-is-of-size {ℓ²} {as = []}     {bs = []}     psz =
  Lift ℓ² ⊤ , lift≃id ∙ is-contr→equiv-⊤ ([] , (λ where [] → refl)) ⁻¹
all2-is-of-size {ℓ²} {as = []}     {bs = b ∷ bs} psz =
  Lift ℓ² ⊥ , lift≃id ∙ ¬→≃⊥ (λ where ()) ⁻¹
all2-is-of-size {ℓ²} {as = a ∷ as} {bs = []}     psz =
  Lift ℓ² ⊥ , lift≃id ∙ ¬→≃⊥ (λ where ()) ⁻¹
all2-is-of-size {ℓ²} {P} {as = a ∷ as} {bs = b ∷ bs} psz =
  let ih = all2-is-of-size {as = as} {bs = bs} psz in
  ≃→is-of-size {A = P a b × All2 P as bs}
    (≅→≃ ((λ where (p , as) → p ∷ as) , iso (λ where (p ∷ as) → p , as)
         (λ where (p ∷ as) → refl)
         λ where (p , as) → refl))
    (×-is-of-size (psz a b) ih)

instance
  Size-All2
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {P : A → B → 𝒰 ℓ¹} {as : List A} {bs : List B}
        ⦃ sp : ∀{a b} → Size ℓ² (P a b) ⦄
      → Size ℓ² (All2 P as bs)
  Size-All2 {ℓ²} .Size.has-of-size = all2-is-of-size λ a b → size ℓ²
  {-# OVERLAPPABLE Size-All2 #-}
