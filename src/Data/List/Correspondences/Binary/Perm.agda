{-# OPTIONS --safe #-}
module Data.List.Correspondences.Binary.Perm where

open import Meta.Prelude
open import Meta.Effect

open import Data.List.Base
open import Data.List.Path
open import Data.List.Operations
open import Data.List.Properties
open import Data.List.Instances.Map
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.Unique
open import Data.Empty.Base
open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Bool.Properties
open import Data.Fin.Computational.Base
open import Data.Sum.Base
open import Data.Reflects.Base as Reflects

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

data Perm {ℓᵃ} {A : 𝒰 ℓᵃ} : List A → List A → 𝒰 ℓᵃ where
  peq    : ∀ {xs ys}
         → xs ＝ ys → Perm xs ys
  pprep  : ∀ {xs ys x y}
         → x ＝ y → Perm xs ys → Perm (x ∷ xs) (y ∷ ys)
  pswap  : ∀ {xs ys x y x′ y′}
         → x ＝ x′ → y ＝ y′ → Perm xs ys → Perm (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
  ptrans : ∀ {xs ys zs}
         → Perm xs ys → Perm ys zs → Perm xs zs

perm-len : {xs ys : List A} → Perm xs ys → length xs ＝ length ys
perm-len (peq e)         = ap length e
perm-len (pprep e p)     = ap suc (perm-len p)
perm-len (pswap ex ey p) = ap (2 +_) (perm-len p)
perm-len (ptrans p₁ p₂)  = perm-len p₁ ∙ perm-len p₂

perm-map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {xs ys : List A} {f : A → B}
         → Perm xs ys → Perm (map f xs) (map f ys)
perm-map {f} (peq e)         = peq (ap (map f) e)
perm-map {f} (pprep e p)     = pprep (ap f e) (perm-map p)
perm-map {f} (pswap ex ey p) = pswap (ap f ex) (ap f ey) (perm-map p)
perm-map     (ptrans p₁ p₂)  = ptrans (perm-map p₁) (perm-map p₂)

perm-nil : {xs : List A} → Perm [] xs → xs ＝ []
perm-nil (peq e)                      = e ⁻¹
perm-nil (ptrans {ys = []}     p₁ p₂) = perm-nil p₂
perm-nil (ptrans {ys = y ∷ ys} p₁ p₂) = false! (perm-nil p₁)

perm-refl : {xs : List A} → Perm xs xs
perm-refl = peq refl

perm-sym : {xs ys : List A} → Perm xs ys → Perm ys xs
perm-sym (peq e)          = peq (e ⁻¹)
perm-sym (pprep e p)      = pprep (e ⁻¹) (perm-sym p)
perm-sym (pswap ex ey p)  = pswap (ey ⁻¹) (ex ⁻¹) (perm-sym p)
perm-sym (ptrans pxy pyz) = ptrans (perm-sym pyz) (perm-sym pxy)

perm-all : {xs ys : List A} {P : Pred A ℓ}
         → Perm xs ys → All P xs → All P ys
perm-all {P} (peq e)          a            = subst (λ q → All P q) e a
perm-all {P} (pprep e p)     (px ∷ a)      = subst P e px ∷ perm-all p a
perm-all {P} (pswap ex ey p) (px ∷ py ∷ a) = subst P ey py ∷ subst P ex px ∷ perm-all p a
perm-all     (ptrans p₁ p₂)   a            = perm-all p₂ $ perm-all p₁ a

perm-any : {xs ys : List A} {P : Pred A ℓ}
         → Perm xs ys → Any P xs → Any P ys
perm-any {P} (peq e)          ax                = subst (λ q → Any P q) e ax
perm-any {P} (pprep e p)     (here px)          = here (subst P e px)
perm-any     (pprep e p)     (there ax)         = there (perm-any p ax)
perm-any {P} (pswap ex ey p) (here px)          = there (here (subst P ex px))
perm-any {P} (pswap ex ey p) (there (here py))  = here (subst P ey py)
perm-any     (pswap ex ey p) (there (there ax)) = there (there (perm-any p ax))
perm-any     (ptrans p₁ p₂)   ax                = perm-any p₂ $ perm-any p₁ ax

perm-cat-comm : {xs ys : List A} → Perm (xs ++ ys) (ys ++ xs)
perm-cat-comm {xs = []}     {ys}          = subst (Perm ys) (++-id-r ys ⁻¹) perm-refl
perm-cat-comm {xs = x ∷ xs} {ys = []}     = subst (λ q → Perm q (x ∷ xs)) (++-id-r (x ∷ xs) ⁻¹) perm-refl
perm-cat-comm {xs = x ∷ xs} {ys = y ∷ ys} =
  ptrans {ys = x ∷ y ∷ xs ++ ys}
    (pprep refl
      (ptrans {ys = y ∷ ys ++ xs}
         (perm-cat-comm {xs = xs})
         (pprep refl (perm-cat-comm {xs = ys}))))
    (ptrans {ys = y ∷ x ∷ xs ++ ys}
      (pswap refl refl perm-refl)
      (pprep refl (perm-cat-comm {xs = x ∷ xs})))

perm-cat-2l : {xs ys zs : List A}
            → Perm xs ys → Perm (zs ++ xs) (zs ++ ys)
perm-cat-2l {zs = []}     p = p
perm-cat-2l {zs = z ∷ zs} p = pprep refl (perm-cat-2l p)

perm-cat-2r : {xs ys zs : List A}
            → Perm xs ys → Perm (xs ++ zs) (ys ++ zs)
perm-cat-2r {xs} {ys} {zs} p = ptrans (perm-cat-comm {xs = xs}) $ ptrans (perm-cat-2l p) (perm-cat-comm {xs = zs})

perm-cat-l : {xs ys zs ws : List A}
           → Perm xs zs → Perm ys ws → Perm (xs ++ ys) (zs ++ ws)
perm-cat-l pxz pyw = ptrans (perm-cat-2r pxz) (perm-cat-2l pyw)

perm-cat-cons-l : {xs ys zs ws : List A} {x : A}
                → Perm xs zs → Perm ys ws → Perm (xs ++ x ∷ ys) (zs ++ x ∷ ws)
perm-cat-cons-l pxz pyw = perm-cat-l pxz (pprep refl pyw)

perm-cons-cat-commassoc : {xs ys : List A} {x : A}
                        → Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
perm-cons-cat-commassoc {xs} {ys} {x} =
  subst (Perm (x ∷ xs ++ ys)) (++-assoc xs (x ∷ []) ys) $
  perm-cat-2r {xs = x ∷ xs} (perm-cat-comm {xs = x ∷ []})

-- bag-equivalence

perm→bag-equiv : {xs ys : List A} → Perm xs ys → xs ≈↔ ys
perm→bag-equiv (peq e)                                     {x = z} = =→≃ (ap (z ∈ₗ_) e)
perm→bag-equiv (pprep {xs} {ys} {x} {y} e p)               {x = z} =
  let ih = perm→bag-equiv p {x = z} in
  ≅→≃ (make-iso (to ih) (fro ih) (make-inverses (re ih) (se ih)))
  where
  to : (z ∈ xs) ≃ (z ∈ ys) → z ∈ (x ∷ xs) → z ∈ (y ∷ ys)
  to _   (here ex)  = here (ex ∙ e)
  to eqv (there hz) = there (eqv $ hz)
  fro : (z ∈ xs) ≃ (z ∈ ys) → z ∈ (y ∷ ys) → z ∈ (x ∷ xs)
  fro _   (here ey)  = here (ey ∙ e ⁻¹)
  fro eqv (there hz) = there (eqv ⁻¹ $ hz)
  re : (eqv : (z ∈ xs) ≃ (z ∈ ys)) → to eqv retraction-of fro eqv
  re eqv = fun-ext λ where
                       (here ey)  → ap here (∙-cancel-r′ (∙-inv-o e))
                       (there hz) → ap there (is-equiv→counit (eqv .snd) hz)
  se : (eqv : (z ∈ xs) ≃ (z ∈ ys)) → to eqv section-of fro eqv
  se eqv = fun-ext λ where
                        (here ex)  → ap here (∙-cancel-r′ (∙-inv-i e))
                        (there hz) → ap there (is-equiv→unit (eqv .snd) hz)
perm→bag-equiv {A} (pswap {xs} {ys} {x} {y} {x′} {y′} ex ey p) {x = z} =
  let ih = perm→bag-equiv p {x = z} in
  ≅→≃ (make-iso (to ih) (fro ih) (make-inverses (re ih) (se ih)))
  where
  to : (z ∈ xs) ≃ (z ∈ ys) → _∈_ {ℙA = List A} z (x ∷ y ∷ xs) → _∈_ {ℙA = List A} z (y′ ∷ x′ ∷ ys)
  to _   (here ez)          = there $ here (ez ∙ ex)
  to _   (there (here ez))  = here (ez ∙ ey)
  to eqv (there (there hz)) = there $ there (eqv $ hz)
  fro : (z ∈ xs) ≃ (z ∈ ys) → _∈_ {ℙA = List A} z (y′ ∷ x′ ∷ ys) → _∈_ {ℙA = List A} z (x ∷ y ∷ xs)
  fro _ (here ez)            = there $ here (ez ∙ ey ⁻¹)
  fro _ (there (here ez))    = here (ez ∙ ex ⁻¹)
  fro eqv (there (there hz)) = there $ there (eqv ⁻¹ $ hz)
  re : (eqv : (z ∈ xs) ≃ (z ∈ ys)) → to eqv retraction-of fro eqv
  re eqv = fun-ext λ where
                       (here ez)          → ap here (∙-cancel-r′ (∙-inv-o ey))
                       (there (here ez))  → ap (there ∘ here) (∙-cancel-r′ (∙-inv-o ex))
                       (there (there hz)) → ap (there ∘ there) (is-equiv→counit (eqv .snd) hz)
  se : (eqv : (z ∈ xs) ≃ (z ∈ ys)) → to eqv section-of fro eqv
  se eqv = fun-ext λ where
                       (here ez)          → ap here (∙-cancel-r′ (∙-inv-i ex))
                       (there (here ez))  → ap (there ∘ here) (∙-cancel-r′ (∙-inv-i ey))
                       (there (there hz)) → ap (there ∘ there) (is-equiv→unit (eqv .snd) hz)
perm→bag-equiv (ptrans p1 p2)                              {x = z} =
  perm→bag-equiv p1 {x = z} ∙ perm→bag-equiv p2 {x = z}

perm→set-equiv : {xs ys : List A} → Perm xs ys → xs ≈ ys
perm→set-equiv {xs} {ys} p = ≈↔→≈ {S = xs} {T = ys} (perm→bag-equiv p)

perm→subset : {xs ys : List A} → Perm xs ys → xs ⊆ ys
perm→subset p = perm→set-equiv p .fst

perm-unique : {xs ys : List A}
            → Perm xs ys → Uniq xs → Uniq ys
perm-unique p u = uniq≈len=→uniq (perm-len p) (perm→set-equiv p) u

-- TODO
-- bag-equiv→perm : {xs ys : List A} → xs ≈↔ ys → Perm xs ys
