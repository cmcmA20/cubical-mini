{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Correspondences.Binary.OPE where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Bool.Base
open import Data.Nat.Order.Base
open import Data.Reflects
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ
  x : A
  xs ys zs : List A

-- aka thinning

data OPE {ℓᵃ} {A : 𝒰 ℓᵃ} : List A → List A → 𝒰 ℓᵃ where
  odone : OPE [] []
  otake : ∀ {x y xs ys}
        → x ＝ y → OPE xs ys → OPE (x ∷ xs) (y ∷ ys)
  odrop : ∀ {xs y ys}
        → OPE xs ys → OPE xs (y ∷ ys)

¬ope-cons-nil : {x : A} {xs : List A}
              → ¬ OPE (x ∷ xs) []
¬ope-cons-nil ()

ope-done? : {xs ys : List A} → OPE xs ys → Bool
ope-done?  odone      = true
ope-done? (otake _ _) = false
ope-done? (odrop _)   = false

ope-take? : {xs ys : List A} → OPE xs ys → Bool
ope-take?  odone      = false
ope-take? (otake _ _) = true
ope-take? (odrop _)   = false

ope-drop? : {xs ys : List A} → OPE xs ys → Bool
ope-drop?  odone      = false
ope-drop? (otake _ _) = false
ope-drop? (odrop _)   = true

ope-init : {xs : List A} → OPE [] xs
ope-init {xs = []}     = odone
ope-init {xs = x ∷ xs} = odrop ope-init

ope-uncons : ∀ {x y} {xs ys : List A}
           → OPE (x ∷ xs) (y ∷ ys) → OPE xs ys
ope-uncons               (otake _ o) = o
ope-uncons {ys = y ∷ ys} (odrop o)   = odrop (ope-uncons o)

ope-refl : {xs : List A}
         → OPE xs xs
ope-refl {xs = []}     = odone
ope-refl {xs = x ∷ xs} = otake refl ope-refl

ope-trans : {xs ys zs : List A}
          → OPE xs ys → OPE ys zs → OPE xs zs
ope-trans  oxy                      odone          = oxy
ope-trans (otake {x} {xs} exy oxy) (otake eyz oyz) = otake (exy ∙ eyz) (ope-trans oxy oyz)
ope-trans (odrop oxy)              (otake eyz oyz) = odrop (ope-trans oxy oyz)
ope-trans  oxy                     (odrop oyz)     = odrop (ope-trans oxy oyz)

instance
  Refl-OPE : Refl {A = List A} OPE
  Refl-OPE .refl = ope-refl

  Trans-OPE : Trans {A = List A} OPE
  Trans-OPE ._∙_ = ope-trans

-- TODO move to properties

ope-length : {xs ys : List A} → OPE xs ys → length xs ≤ length ys
ope-length  odone      = z≤
ope-length (otake _ l) = s≤s (ope-length l)
ope-length (odrop l)   = ≤-trans (ope-length l) ≤-ascend

ope-antisym : {xs ys : List A}
            → OPE xs ys → OPE ys xs → xs ＝ ys
ope-antisym  odone           _            = refl
ope-antisym (otake exy oxy) (otake _ oyx) = ap² _∷_ exy (ope-antisym oxy oyx)
ope-antisym (otake _ oxy)   (odrop oyx)   = false! $ ≤-trans (ope-length oyx) (ope-length oxy)
ope-antisym (odrop oxy)     (otake _ oyx) = false! $ ≤-trans (ope-length oxy) (ope-length oyx)
ope-antisym (odrop oxy)     (odrop oyx)   = false! $ ≤≃≤+r {n = 2} ⁻¹ $ ≤-trans (s≤s $ ope-length oxy) (ope-length oyx)

ope-id-l : {A : 𝒰 ℓᵃ} {xs ys : List A}
         → (o : OPE xs ys) → refl ∙ o ＝ o
ope-id-l  odone      = refl
ope-id-l (otake e o) = ap² otake (∙-id-o e) (ope-id-l o)
ope-id-l (odrop o)   = ap odrop (ope-id-l o)

ope-id-r : {A : 𝒰 ℓᵃ} {xs ys : List A}
         → (o : OPE xs ys) → o ∙ refl ＝ o
ope-id-r  odone      = refl
ope-id-r (otake e o) = ap² otake (∙-id-i e) (ope-id-r o)
ope-id-r (odrop o)   = ap odrop (ope-id-r o)

ope-assoc : {A : 𝒰 ℓᵃ} {xs ys zs ws : List A}
          → (o : OPE xs ys) (p : OPE ys zs) (q : OPE zs ws)
          → o ∙ p ∙ q ＝ (o ∙ p) ∙ q
ope-assoc  o            p            odone       = refl
ope-assoc (otake eo o) (otake ep p) (otake eq q) = ap² otake (∙-assoc eo ep eq) (ope-assoc o p q)
ope-assoc (odrop o)    (otake ep p) (otake eq q) = ap odrop (ope-assoc o p q)
ope-assoc  o           (odrop p)    (otake eq q) = ap odrop (ope-assoc o p q)
ope-assoc  o            p           (odrop q)    = ap odrop (ope-assoc o p q)

ope-init-unique : {xs : List A}
                → (o : OPE [] xs) → o ＝ ope-init
ope-init-unique  odone    = refl
ope-init-unique (odrop o) = ap odrop (ope-init-unique o)

ope→subset : {xs ys : List A}
           → OPE xs ys → xs ⊆ ys
ope→subset (otake e o) (here e′)  = here (e′ ∙ e)
ope→subset (otake e o) (there hx) = there (ope→subset o hx)
ope→subset (odrop o)    hx        = there (ope→subset o hx)

instance
  HUnit-o-≤ : HUnit-o {A = List A} OPE
  HUnit-o-≤ .∙-id-o = ope-id-l

  HUnit-i-≤ : HUnit-i {A = List A} OPE
  HUnit-i-≤ .∙-id-i = ope-id-r

  HAssoc-≤ : HAssoc {A = List A} OPE
  HAssoc-≤ .∙-assoc = ope-assoc
