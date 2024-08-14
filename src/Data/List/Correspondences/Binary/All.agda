{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.All where

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
  @0 zs : List C

data All² {ℓᵃ ℓᵇ ℓ¹} {A : Type ℓᵃ} {B : Type ℓᵇ}
          (R : A → B → 𝒰 ℓ¹) : @0 List A → @0 List B → Type (ℓᵃ ⊔ ℓᵇ ⊔ ℓ¹) where
  []  : All² R [] []
  _∷_ : R x y → All² R xs ys → All² R (x ∷ xs) (y ∷ ys)

module _ {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {R : A → B → 𝒰 ℓ¹}
         ⦃ ep : {a : A} {b : B} → Extensional (R a b) ℓ¹ ⦄ where
  Code-All² : {xs : List A} {ys : List B} (p q : All² R xs ys) → 𝒰 ℓ¹
  Code-All² {xs = []}     {ys = []}     []       []       = ⊤
  Code-All² {xs = x ∷ xs} {ys = y ∷ ys} (px ∷ p) (qx ∷ q) = ep .Pathᵉ px qx × Code-All² p q

  code-all²-refl : {xs : List A} {ys : List B} (p : All² R xs ys) → Code-All² p p
  code-all²-refl {xs = []}     {ys = []}     []       = _
  code-all²-refl {xs = x ∷ xs} {ys = y ∷ ys} (px ∷ p) = ep .reflᵉ px , code-all²-refl p

  decode-all² : {xs : List A} {ys : List B} {p q : All² R xs ys} (c : Code-All² p q) → p ＝ q
  decode-all² {xs = []}     {ys = []}     {p = []}     {q = []}      _       = refl
  decode-all² {xs = x ∷ xs} {ys = y ∷ ys} {p = px ∷ p} {q = qx ∷ q} (cx , c) =
    ap² {C = λ _ _ → All² R (x ∷ xs) (y ∷ ys)} _∷_ (ep .idsᵉ .to-path cx) (decode-all² c)

  decode-all²-refl
    : {xs : List A} {ys : List B} {p q : All² R xs ys} (c : Code-All² p q)
    → code-all²-refl p ＝[ ap (Code-All² p) (decode-all² c) ]＝ c
  decode-all²-refl {xs = []}     {ys = []}     {p = []}     {q = []}     _         = refl
  decode-all²-refl {xs = x ∷ xs} {ys = y ∷ ys} {p = px ∷ p} {q = qx ∷ q} (cx , c)  =
    ep .idsᵉ .to-path-over cx ,ₚ decode-all²-refl c

  Extensional-All² : {xs : List A} {ys : List B} → Extensional (All² R xs ys) ℓ¹
  Extensional-All² .Pathᵉ              = Code-All²
  Extensional-All² .reflᵉ              = code-all²-refl
  Extensional-All² .idsᵉ .to-path      = decode-all²
  Extensional-All² .idsᵉ .to-path-over = decode-all²-refl

opaque
  code-all²-is-of-hlevel
    : ∀ {n} {xs : List A} {ys : List B} {u v : All² R xs ys}
    → (∀ x y → is-of-hlevel (suc n) (R x y))
    → is-of-hlevel n (Code-All² u v)
  code-all²-is-of-hlevel {n} {xs = []}     {ys = []}     {u = []}     {v = []}     hl = hlevel n
  code-all²-is-of-hlevel {n} {xs = x ∷ xs} {ys = y ∷ ys} {u = ux ∷ u} {v = vx ∷ v} hl =
    ×-is-of-hlevel n (path-is-of-hlevel n (hl x y) ux vx) (code-all²-is-of-hlevel hl)

-- All² cannot be made contractible because the lists might not match
all²-is-of-hlevel
  : (n : HLevel) {xs : List A} {ys : List B}
  → (∀ x y → is-of-hlevel (suc n) (R x y))
  → is-of-hlevel (suc n) (All² R xs ys)
all²-is-of-hlevel n hl =
  identity-system→is-of-hlevel n (Extensional-All² .idsᵉ) (λ x y → code-all²-is-of-hlevel hl)

instance opaque
  H-Level-All² : ∀ {n} {xs : List A} {ys : List B} → ⦃ n ≥ʰ 1 ⦄ → ⦃ A-hl : ∀ {x y} → H-Level n (R x y) ⦄ → H-Level n (All² R xs ys)
  H-Level-All² {n} ⦃ s≤ʰs _ ⦄ .H-Level.has-of-hlevel = all²-is-of-hlevel _ (λ x y → hlevel n)
  {-# OVERLAPPING H-Level-All² #-}

all²-++ : {@0 as xs : List A} → {@0 bs ys : List B}
        → All² R as bs → All² R xs ys → All² R (as ++ xs) (bs ++ ys)
all²-++ []        rxy = rxy
all²-++ (r ∷ rab) rxy = r ∷ all²-++ rab rxy

all²-split : {as : List A} {@0 xs : List A} {bs : List B} {@0 ys : List B}
           → length as ＝ length bs
           → All² R (as ++ xs) (bs ++ ys) → All² R as bs × All² R xs ys
all²-split {as = []}     {bs = []}     _  rs      = [] , rs
all²-split {as = []}     {bs = b ∷ bs} e  rs      = absurd (zero≠suc e)
all²-split {as = a ∷ as} {bs = []}     e  rs      = absurd (suc≠zero e)
all²-split {as = a ∷ as} {bs = x ∷ bs} e (r ∷ rs) =
  let (rab , rxy) = all²-split (suc-inj e) rs in (r ∷ rab) , rxy

all²-map : {@0 xs : List A} {@0 ys : List B}
         → ∀ᴱ[ R ⇒ Q ]
         → All² R xs ys → All² Q xs ys
all²-map     f []       = []
all²-map {R} f (r ∷ rs) = f r ∷ all²-map {R = R} f rs

all²-replicate-l : {x : A} {ys : List B}
                 → Π[ R x ]
                 → All² R (replicate (length ys) x) ys
all²-replicate-l {ys = []}     h = []
all²-replicate-l {ys = y ∷ ys} h = h y ∷ all²-replicate-l h

all²-replicate-r : {xs : List A} {y : B}
                 → Π[ flip R y ]
                 → All² R xs (replicate (length xs) y)
all²-replicate-r {xs = []}     h = []
all²-replicate-r {xs = x ∷ xs} h = h x ∷ all²-replicate-r h

all²-antisym : {as bs : List A}
               {P : A → A → 𝒰 ℓ¹}
             → (∀ a b → P a b → P b a → a ＝ b)
             → All² P as bs → All² P bs as → as ＝ bs
all²-antisym     {as = []}     {bs = []}     pa []        []          = refl
all²-antisym {A} {as = a ∷ as} {bs = b ∷ bs} pa (ab ∷ abs) (ba ∷ bas) =
  ap² {C = λ _ _ → List A} _∷_ (pa a b ab ba) (all²-antisym pa abs bas)

all²-refl : {as : List A} {P : A → A → 𝒰 ℓ¹}
          → ⦃ Reflexive P ⦄
          → All² P as as
all²-refl {as = []}     = []
all²-refl {as = a ∷ as} = refl ∷ all²-refl

-- monotype version
all²-∙ : {@0 as bs cs : List A}
         {P : A → A → 𝒰 ℓ¹}
       → ⦃ Transitive P ⦄
       → All² P as bs → All² P bs cs → All² P as cs
all²-∙ []         []         = []
all²-∙ (ab ∷ abs) (bc ∷ bcs) = ab ∙ bc ∷ all²-∙ abs bcs

instance
  Refl-All² : ⦃ Reflexive P ⦄ → Reflexive (λ xs ys → All² P xs ys)
  Refl-All² .refl = all²-refl

  Trans-All² : ⦃ Transitive P ⦄ → Transitive (λ xs ys → All² P xs ys)
  Trans-All² ._∙_ = all²-∙

all²-is-of-size : {P : A → B → 𝒰 ℓ¹} {as : List A} {bs : List B}
                → (∀ a b → is-of-size ℓ² (P a b))
                → is-of-size ℓ² (All² P as bs)
all²-is-of-size {ℓ²} {as = []}     {bs = []}     psz =
  ⊤ , lift≃id ∙ is-contr→equiv-⊤ ([] , (λ where [] → refl)) ⁻¹
all²-is-of-size {ℓ²} {as = []}     {bs = b ∷ bs} psz =
  ⊥ , lift≃id ∙ ¬→≃⊥ (λ where ()) ⁻¹
all²-is-of-size {ℓ²} {as = a ∷ as} {bs = []}     psz =
  ⊥ , lift≃id ∙ ¬→≃⊥ (λ where ()) ⁻¹
all²-is-of-size {ℓ²} {P} {as = a ∷ as} {bs = b ∷ bs} psz =
  ≃→is-of-size {A = P a b × All² P as bs}
    (≅→≃ ((λ where (p , as) → p ∷ as) , iso (λ where (p ∷ as) → p , as)
         (λ where (p ∷ as) → refl) λ where (p , as) → refl))
    (×-is-of-size (psz a b) (all²-is-of-size {as = as} {bs = bs} psz))

instance
  Size-All²
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {P : A → B → 𝒰 ℓ¹} {as : List A} {bs : List B}
        ⦃ sp : ∀{a b} → Size ℓ² (P a b) ⦄
      → Size ℓ² (All² P as bs)
  Size-All² {ℓ²} .Size.has-of-size = all²-is-of-size λ a b → size ℓ²
  {-# OVERLAPPABLE Size-All² #-}
