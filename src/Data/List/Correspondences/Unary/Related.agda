{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Related where

open import Meta.Prelude
open import Meta.Extensionality

open import Data.Empty.Base as ⊥
open import Data.Unit.Base
open import Data.Reflects.Base
open import Data.List.Base
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.At

private variable
  ℓ ℓᵃ : Level
  A : 𝒰 ℓᵃ
  P Q R : A → A → 𝒰 ℓ
  @0 x0 : A
  @0 xs ys : List A

infixr 5 _∷ʳ_
data Related {ℓ ℓᵃ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : @0 A → @0 List A → 𝒰 (ℓ ⊔ ℓᵃ) where
  []ʳ  : ∀ {x} → Related R x []
  _∷ʳ_ : ∀ {x0 x xs} → R x0 x → Related R x xs → Related R x0 (x ∷ xs)

module _ {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ}
         ⦃ ep : {a b : A} → Extensional (R a b) ℓ ⦄ where
  Code-Related : {x0 : A} {xs : List A} (p q : Related R x0 xs) → 𝒰 ℓ
  Code-Related {xs = []}     []ʳ       []ʳ       = ⊤
  Code-Related {xs = x ∷ xs} (px ∷ʳ p) (qx ∷ʳ q) = ep .Pathᵉ px qx × Code-Related p q

  code-related-refl : {x0 : A} {xs : List A} (p : Related R x0 xs) → Code-Related p p
  code-related-refl {xs = []}     []ʳ       = lift tt
  code-related-refl {xs = x ∷ xs} (px ∷ʳ p) = ep .reflᵉ px , code-related-refl p

  decode-related : {x0 : A} {xs : List A} {p q : Related R x0 xs} (c : Code-Related p q) → p ＝ q
  decode-related      {xs = []}     {p = []ʳ}     {q = []ʳ}      _       = refl
  decode-related {x0} {xs = x ∷ xs} {p = px ∷ʳ p} {q = qx ∷ʳ q} (cx , c) =
    ap² {C = λ _ _ → Related R x0 (x ∷ xs)} _∷ʳ_ (ep .idsᵉ .to-path cx) (decode-related c)

  decode-related-refl
    : {x0 : A} {xs : List A} {p q : Related R x0 xs} (c : Code-Related p q)
    → code-related-refl p ＝[ ap (Code-Related p) (decode-related c) ]＝ c
  decode-related-refl {xs = []}     {p = []ʳ}     {q = []ʳ}     _         = refl
  decode-related-refl {xs = x ∷ xs} {p = px ∷ʳ p} {q = qx ∷ʳ q} (cx , c)  =
    ep .idsᵉ .to-path-over cx ,ₚ decode-related-refl c

  Extensional-Related : {x0 : A} {xs : List A} → Extensional (Related R x0 xs) ℓ
  Extensional-Related .Pathᵉ              = Code-Related
  Extensional-Related .reflᵉ              = code-related-refl
  Extensional-Related .idsᵉ .to-path      = decode-related
  Extensional-Related .idsᵉ .to-path-over = decode-related-refl

opaque
  code-related-is-of-hlevel
    : ∀ {n} {x0 : A} {xs : List A} {u v : Related R x0 xs}
    → (∀ x y → is-of-hlevel (suc n) (R x y))
    → is-of-hlevel n (Code-Related u v)
  code-related-is-of-hlevel {n}      {xs = []}     {u = []ʳ}     {v = []ʳ}     hl = hlevel n
  code-related-is-of-hlevel {n} {x0} {xs = x ∷ xs} {u = ux ∷ʳ u} {v = vx ∷ʳ v} hl =
    ×-is-of-hlevel n (path-is-of-hlevel n (hl x0 x) ux vx)
                     (code-related-is-of-hlevel {xs = xs} hl)

related-is-contr
    : {R : A → A → 𝒰 ℓ} {x0 : A} {xs : List A}
    → (∀ x y → is-contr (R x y))
    → is-contr (Related R x0 xs)
related-is-contr     {xs = []}     cntr = []ʳ , λ where []ʳ → refl
related-is-contr {R} {x0} {xs = x ∷ xs} cntr =
 let (xc , xeq) = cntr x0 x
     (ac , aeq) = related-is-contr {xs = xs} cntr
  in
    xc ∷ʳ ac
  , λ where (px ∷ʳ pxs) → ap² {C = λ _ _ → Related R x0 (x ∷ xs)} _∷ʳ_ (xeq px) (aeq pxs)

related-is-of-hlevel
  : (n : HLevel) {x0 : A} {xs : List A}
  → (∀ x y → is-of-hlevel n (R x y))
  → is-of-hlevel n (Related R x0 xs)
related-is-of-hlevel  zero        hl = related-is-contr hl
related-is-of-hlevel (suc n) {xs} hl =
  identity-system→is-of-hlevel n (Extensional-Related .idsᵉ) (λ x y → code-related-is-of-hlevel {xs = xs} hl)

instance opaque
  H-Level-Related : ∀ {n} {x0 : A} {xs : List A} → ⦃ A-hl : ∀ {x y} → H-Level n (R x y) ⦄ → H-Level n (Related R x0 xs)
  H-Level-Related {n} .H-Level.has-of-hlevel = related-is-of-hlevel _  (λ _ _ → hlevel n)
  {-# OVERLAPPING H-Level-Related #-}

-- transitive R

related-weaken : {x0 y0 : A} {xs : List A} → ⦃ Trans R ⦄
               → R y0 x0 → Related R x0 xs → Related R y0 xs
related-weaken {xs = []}     ryx []ʳ       = []ʳ
related-weaken {xs = x ∷ xs} ryx (rx ∷ʳ r) = ryx ∙ rx ∷ʳ r

{- TODO indexed by predicate -}
related→all : {x0 : A} {xs : List A} → ⦃ Trans R ⦄
            → Related R x0 xs → All (R x0) xs
related→all {xs = []}     []ʳ       = []
related→all {xs = x ∷ xs} (rx ∷ʳ r) =
  rx ∷ all-map (rx ∙_) (related→all {x0 = x} {xs = xs} r)


{- sorted -}

data Sorted {ℓ ℓᵃ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : @0 List A → 𝒰 (ℓ ⊔ ℓᵃ) where
  []ˢ : Sorted R []
  ∷ˢ  : ∀ {x xs} → Related R x xs → Sorted R (x ∷ xs)

module _ {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ}
         ⦃ ep : {a b : A} → Extensional (R a b) ℓ ⦄ where
  Code-Sorted : {xs : List A} (p q : Sorted R xs) → 𝒰 ℓ
  Code-Sorted {xs = []}     []ˢ    []ˢ    = ⊤
  Code-Sorted {xs = x ∷ xs} (∷ˢ p) (∷ˢ q) = Code-Related p q

  code-sorted-refl : {xs : List A} (p : Sorted R xs) → Code-Sorted p p
  code-sorted-refl {xs = []}     []ˢ    = lift tt
  code-sorted-refl {xs = x ∷ xs} (∷ˢ p) = code-related-refl p

  decode-sorted : {xs : List A} {p q : Sorted R xs} (c : Code-Sorted p q) → p ＝ q
  decode-sorted {xs = []}     {p = []ˢ}  {q = []ˢ}  _ = refl
  decode-sorted {xs = x ∷ xs} {p = ∷ˢ p} {q = ∷ˢ q} c = ap ∷ˢ (decode-related c)

  decode-sorted-refl
    : {xs : List A} {p q : Sorted R xs} (c : Code-Sorted p q)
    → code-sorted-refl p ＝[ ap (Code-Sorted p) (decode-sorted c) ]＝ c
  decode-sorted-refl {xs = []}     {p = []ˢ}  {q = []ˢ}  _ = refl
  decode-sorted-refl {xs = x ∷ xs} {p = ∷ˢ p} {q = ∷ˢ q} c = decode-related-refl c

  Extensional-Sorted : {xs : List A} → Extensional (Sorted R xs) ℓ
  Extensional-Sorted .Pathᵉ                      = Code-Sorted
  Extensional-Sorted .reflᵉ                      = code-sorted-refl
  Extensional-Sorted .idsᵉ .to-path              = decode-sorted
  Extensional-Sorted .idsᵉ .to-path-over {a} {b} = decode-sorted-refl {p = a} {q = b}

opaque
  code-sorted-is-of-hlevel
    : ∀ {n} {xs : List A} {u v : Sorted R xs}
    → (∀ x y → is-of-hlevel (suc n) (R x y))
    → is-of-hlevel n (Code-Sorted u v)
  code-sorted-is-of-hlevel {n} {xs = []}     {u = []ˢ}  {v = []ˢ}  hl = hlevel n
  code-sorted-is-of-hlevel {n} {xs = x ∷ xs} {u = ∷ˢ u} {v = ∷ˢ v} hl = code-related-is-of-hlevel {xs = xs} hl

sorted-is-contr
    : {R : A → A → 𝒰 ℓ} {xs : List A}
    → (∀ x y → is-contr (R x y))
    → is-contr (Sorted R xs)
sorted-is-contr     {xs = []}     cntr = []ˢ , λ where []ˢ → refl
sorted-is-contr {R} {xs = x ∷ xs} cntr =
  let (c , eq) = related-is-contr {x0 = x} {xs = xs} cntr in
  (∷ˢ c) ,
    λ where (∷ˢ sxs) → ap ∷ˢ (eq sxs)

sorted-is-of-hlevel
  : (n : HLevel) {xs : List A}
  → (∀ x y → is-of-hlevel n (R x y))
  → is-of-hlevel n (Sorted R xs)
sorted-is-of-hlevel  zero   hl = sorted-is-contr hl
sorted-is-of-hlevel (suc n) hl =
  identity-system→is-of-hlevel n (Extensional-Sorted .idsᵉ) (λ x y → code-sorted-is-of-hlevel {u = x} {v = y} hl)

instance opaque
  H-Level-Sorted : ∀ {n} {xs : List A} → ⦃ A-hl : ∀ {x y} → H-Level n (R x y) ⦄ → H-Level n (Sorted R xs)
  H-Level-Sorted {n} .H-Level.has-of-hlevel = sorted-is-of-hlevel _  (λ _ _ → hlevel n)
  {-# OVERLAPPING H-Level-Sorted #-}

related→sorted : {x0 : A} {xs : List A}
               → Related R x0 xs → Sorted R xs
related→sorted {xs = []}     r        = []ˢ
related→sorted {xs = x ∷ xs} (_ ∷ʳ r) = ∷ˢ r

sorted-at0→related : {x0 : A} {xs : List A}
                   → Sorted R xs → AtWeak (R x0) xs 0
                   → Related R x0 xs
sorted-at0→related {xs = []} []ˢ awnil = []ʳ
sorted-at0→related {xs = x ∷ xs} (∷ˢ r) (awhere px) = px ∷ʳ r
