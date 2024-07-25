{-# OPTIONS --safe #-}
module Foundations.Isomorphism where

open import Foundations.Base
  hiding (inv)
open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  f : A → B

is-isoᴱ : (f : A → B) → Type _
is-isoᴱ {A} {B} f = Σ[ inv ꞉ (B → A) ]
  ( Erased (inv is-right-inverse-of f)
  × Erased (inv is-left-inverse-of  f) )

Isoᴱ : Type ℓ → Type ℓ′ → Type _
Isoᴱ A B = Σ[ f ꞉ (A → B) ] is-isoᴱ f

is-equivᴱ→is-isoᴱ : is-equivᴱ f → is-isoᴱ f
is-equivᴱ→is-isoᴱ {f} eqv = is-equivᴱ→inverse eqv
                          , erase (λ y → eqv y .fst .snd .erased)
                          , erase (λ x i → eqv (f x) .snd .erased (x , erase refl) i .fst)


record is-iso (f : A → B) : Type (level-of-type A ⊔ level-of-type B) where
  no-eta-equality
  constructor iso
  field
    inv  : B → A
    rinv : inv is-right-inverse-of f
    linv : inv is-left-inverse-of  f

  forward-injective : (x y : A) (p : f x ＝ f y) → x ＝ y
  forward-injective x y p = sym (linv x) ∙∙ ap inv p ∙∙ linv y

  inverse-injective : (x y : B) (p : inv x ＝ inv y) → x ＝ y
  inverse-injective x y p = sym (rinv x) ∙∙ ap f p ∙∙ rinv y

open is-iso

is-iso→is-isoᴱ : is-iso f → is-isoᴱ f
is-iso→is-isoᴱ f-iso = inv f-iso , erase (rinv f-iso) , erase (linv f-iso)

is-iso-inv : (r : is-iso f) → is-iso (r . inv)
is-iso-inv {f} r .inv  = f
is-iso-inv     r .rinv = r .linv
is-iso-inv     r .linv = r .rinv

Iso : Type ℓ → Type ℓ′ → Type _
Iso A B = Σ[ f ꞉ (A → B) ] is-iso f

_≅_ = Iso
infix 1 _≅_

id-is-iso : is-iso {A = A} id
id-is-iso .inv = id
id-is-iso .rinv = λ _ → refl
id-is-iso .linv = λ _ → refl

is-iso-comp : {g : B → C} → is-iso f → is-iso g → is-iso (g ∘ f)
is-iso-comp     r s .inv    = r .inv ∘ s .inv
is-iso-comp {g} r s .rinv z = ap g        (r .rinv (s .inv z)) ∙ s .rinv z
is-iso-comp {f} r s .linv x = ap (r .inv) (s .linv (f      x)) ∙ r .linv x

instance
  Refl-Iso : Refl (Iso {ℓ})
  Refl-Iso .refl = id , id-is-iso

  Refl-Erased-Iso : Refl (Isoᴱ {ℓ})
  Refl-Erased-Iso .refl = id , is-iso→is-isoᴱ id-is-iso

  Symm-Iso : Symm (Iso {ℓ} {ℓ′}) Iso
  Symm-Iso ._⁻¹ r = r .snd .inv , is-iso-inv (r .snd)

  Symm-Erased-Iso : Symm (Isoᴱ {ℓ} {ℓ′}) Isoᴱ
  Symm-Erased-Iso ._⁻¹ (f , g , r , l) = g , f , l , r

  Trans-Iso : Trans (Iso {ℓ} {ℓ′}) (Iso {ℓ′ = ℓ″}) Iso
  Trans-Iso ._∙_ (f , f-iso) (f′ , f′-iso) = f′ ∘ f , is-iso-comp f-iso f′-iso

  Trans-Erased-Iso : Trans (Isoᴱ {ℓ} {ℓ′}) (Isoᴱ {ℓ′ = ℓ″}) Isoᴱ
  Trans-Erased-Iso ._∙_ (f , g , erase r , erase l) (f′ , g′ , erase r′ , erase l′)
    = f′ ∘ f  , g ∘ g′
    , erase (λ x → ap f′ (r (g′ x)) ∙ r′ x)
    , erase (λ x → ap g  (l′ (f x)) ∙ l  x)

  Funlike-Iso : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (Iso A B) A (λ _ → B)
  Funlike-Iso ._#_ = fst

  Funlike-Erased-Iso : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (Isoᴱ A B) A (λ _ → B)
  Funlike-Erased-Iso ._#_ = fst

id-composition→is-iso : (r : is-iso f) (g : B → A) (p : f ∘ g ＝ id) → is-iso g
id-composition→is-iso {f} r g p .inv = f
id-composition→is-iso {f} r g p .rinv y = sym (r .linv (g (f y))) ∙∙ ap (λ φ → r .inv (φ (f y))) p ∙∙ r .linv y
id-composition→is-iso     r g p .linv y = ap (_$ y) p

is-equiv→is-iso : is-equiv f → is-iso f
is-iso.inv  (is-equiv→is-iso eqv) = is-equiv→inverse eqv
is-iso.rinv (is-equiv→is-iso eqv) y = eqv .equiv-proof y .fst .snd
is-iso.linv (is-equiv→is-iso {f} eqv) x i = eqv .equiv-proof (f x) .snd (x , refl) i .fst

module _ {f : A → B} (r : is-iso f) where
  open is-iso r renaming ( inv  to g
                         ; rinv to u
                         ; linv to v
                         )
  module _ (y : B) (x₀ x₁ : A) (p₀ : f x₀ ＝ y) (p₁ : f x₁ ＝ y) where

    private
      π₀ : g y ＝ x₀
      π₀ i = hcomp (∂ i) λ where
        k (i = i0) → g y
        k (i = i1) → v x₀ k
        k (k = i0) → g (p₀ (~ i))

      θ₀ : Square (ap g (sym p₀)) refl π₀ (v x₀)
      θ₀ i j = hfill (∂ i) j λ where
        k (i = i0) → g y
        k (i = i1) → v x₀ k
        k (k = i0) → g (p₀ (~ i))

      π₁ : g y ＝ x₁
      π₁ i = hcomp (∂ i) λ where
        j (i = i0) → g y
        j (i = i1) → v x₁ j
        j (j = i0) → g (p₁ (~ i))

      θ₁ : Square (ap g (sym p₁)) refl π₁ (v x₁)
      θ₁ i j = hfill (∂ i) j λ where
        j (i = i0) → g y
        j (i = i1) → v x₁ j
        j (j = i0) → g (p₁ (~ i))

      π : x₀ ＝ x₁
      π i = hcomp (∂ i) λ where
        j (j = i0) → g y
        j (i = i0) → π₀ j
        j (i = i1) → π₁ j

      θ : Square refl π₀ π π₁
      θ i j = hfill (∂ i) j λ where
        k (i = i1) → π₁ k
        k (i = i0) → π₀ k
        k (k = i0) → g y

      ι : Square (ap (g ∘ f) π) (ap g p₀) refl (ap g p₁)
      ι i j = hcomp (∂ i ∨ ∂ j) λ where
        k (k = i0) → θ i (~ j)
        k (i = i0) → θ₀ (~ j) (~ k)
        k (i = i1) → θ₁ (~ j) (~ k)
        k (j = i0) → v (π i) (~ k)
        k (j = i1) → g y

      sq₁ : Square (ap f π) p₀ refl p₁
      sq₁ i j = hcomp (∂ i ∨ ∂ j) λ where
         k (i = i0) → u (p₀ j) k
         k (i = i1) → u (p₁ j) k
         k (j = i0) → u (f (π i)) k
         k (j = i1) → u y k
         k (k = i0) → f (ι i j)

    is-iso→fibre-is-prop : (x₀ , p₀) ＝ (x₁ , p₁)
    is-iso→fibre-is-prop i .fst = π i
    is-iso→fibre-is-prop i .snd = sq₁ i

  is-iso→is-equiv : is-equiv f
  is-iso→is-equiv .equiv-proof y .fst .fst = g y
  is-iso→is-equiv .equiv-proof y .fst .snd = u y
  is-iso→is-equiv .equiv-proof y .snd z =
    is-iso→fibre-is-prop y (g y) (fst z) (u y) (snd z)

≅→≃ : Iso A B → A ≃ B
≅→≃ (f , is-iso) = f , is-iso→is-equiv is-iso
