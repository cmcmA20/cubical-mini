{-# OPTIONS --safe #-}
module Foundations.Base where

open import Foundations.Prim.Interval public
import Foundations.Prim.Empty as ⊥
open ⊥ using (⊥ₜ) public
open import Foundations.Prim.Kan public
import Foundations.Prim.Sum as ⊎
open ⊎ using (_⊎_; inl; inr) public
open import Foundations.Prim.Type public

open import Foundations.Cat.Reflexivity public
open import Foundations.Cat.Composition public
open import Foundations.Cat.Diagram.Coproduct.Binary public
open import Foundations.Cat.Diagram.Coproduct.Indexed public
open import Foundations.Cat.Diagram.Exponential public
open import Foundations.Cat.Diagram.Initial public
open import Foundations.Cat.Diagram.Product.Binary public
open import Foundations.Cat.Diagram.Product.Indexed public
open import Foundations.Cat.Diagram.Terminal public
open import Foundations.Cat.Symmetry public
open import Foundations.Cat.Underlying public

open import Agda.Builtin.Sigma public
  renaming (Σ to Σₜ)
open import Agda.Builtin.Unit public
  renaming (⊤ to ⊤ₜ)

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd ℓi ℓf : Level
  A B : Type ℓ

-- We reside in the double ∞-category of types, functions and binary correspondences, let's get comfy
instance
  Refl-Fun : Refl (λ ℓ → Type ℓ) Fun
  Refl-Fun .refl x = x

  Comp-Fun : Comp (λ ℓ → Type ℓ) Fun
  Comp-Fun ._∙_ f g x = g (f x)

  Underlying-Fun : Underlying (λ ℓ → Type ℓ) Fun
  Underlying-Fun .ℓ-und ℓ = ℓ
  Underlying-Fun .⌞_⌟ X = X

  Refl-Corr² : Refl (λ _ → Type ℓ) (Corr² ℓ)
  Refl-Corr² .refl = _＝_

  Comp-Corr² : Comp (λ _ → Type ℓ) (Corr² ℓ)
  Comp-Corr² ._∙_ {x = A} {y = B} {z = C} R S a c = Σₜ B λ b → Σₜ (R a b) (λ _ → S b c)

  Symmetry-Corr : Symmetry (λ _ → Type ℓ) (Corr² ℓ)
  Symmetry-Corr .sym R B A = R A B

{-# INCOHERENT Refl-Fun Comp-Fun Underlying-Fun
               Refl-Corr² Symmetry-Corr Comp-Corr²
#-}


module _ where
  open Initial
  open Terminal

  instance
    Initial-Fun : Initial (λ ℓ → Type ℓ) Fun
    Initial-Fun .⊥ = ⊥ₜ
    Initial-Fun .has-is-init _ .centre ()
    Initial-Fun .has-is-init _ .paths _ _ ()

    Terminal-Fun : Terminal (λ ℓ → Type ℓ) Fun
    Terminal-Fun .⊤ = ⊤ₜ
    Terminal-Fun .has-is-terminal _ .centre _ = tt
    Terminal-Fun .has-is-terminal _ .paths _ _ _ = tt
{-# INCOHERENT Initial-Fun Terminal-Fun #-}

module _ where
  open Binary-coproducts
  open Coproduct
  open Binary-products
  open Product

  instance
    Binary-coproducts-Fun : Binary-coproducts (λ ℓ → Type ℓ) Fun
    Binary-coproducts-Fun ._⨿_ = _⊎_
    Binary-coproducts-Fun .has-coproduct .ι₁ = inl
    Binary-coproducts-Fun .has-coproduct .ι₂ = inr
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅_,_⁆ = ⊎.rec
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆∘ι₁ {f} _ = f
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆∘ι₂ {g} _ = g
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆-unique fs sn i (inl x) = fs i x
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆-unique fs sn i (inr x) = sn i x

    Binary-products-Fun : Binary-products (λ ℓ → Type ℓ) Fun
    Binary-products-Fun ._×_ A B = Σₜ A λ _ → B
    Binary-products-Fun .has-product .π₁ = fst
    Binary-products-Fun .has-product .π₂ = snd
    Binary-products-Fun .has-product .has-is-product .⟨_,_⟩ f g q = f q , g q
    Binary-products-Fun .has-product .has-is-product .π₁∘⟨⟩ {f} _ = f
    Binary-products-Fun .has-product .has-is-product .π₂∘⟨⟩ {g} _ = g
    Binary-products-Fun .has-product .has-is-product .⟨⟩-unique fs sn i q = fs i q , sn i q
{-# INCOHERENT Binary-coproducts-Fun Binary-products-Fun #-}

infixr 70 _⨿ₜ_
_⨿ₜ_ : Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
_⨿ₜ_ = _⨿_ ⦃ _ ⦄ ⦃ Binary-coproducts-Fun ⦄
{-# INLINE _⨿ₜ_ #-}

infixr 80 _×ₜ_
_×ₜ_ : Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
_×ₜ_ = _×_ ⦃ _ ⦄ ⦃ Binary-products-Fun ⦄
{-# INLINE _×ₜ_ #-}


module _ where
  open Cartesian-closed
  open Exponential

  instance
    Cartesian-closed-Fun : Cartesian-closed (λ ℓ → Type ℓ) Fun
    Cartesian-closed-Fun ._⇒_ = Fun
    Cartesian-closed-Fun .has-exp .ev (f , x) = f x
    Cartesian-closed-Fun .has-exp .has-is-exp .ƛ w g a = w (g , a)
    Cartesian-closed-Fun .has-exp .has-is-exp .ƛ-commutes m _ = m
    Cartesian-closed-Fun .has-exp .has-is-exp .ƛ-unique _ p i g a = p i (g , a)
    {-# INCOHERENT Cartesian-closed-Fun #-}

infixr 0 ¬ₜ_
¬ₜ_ : Type ℓ → Type ℓ
¬ₜ_ = ¬_ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ Cartesian-closed-Fun  ⦄
{-# INLINE ¬ₜ_ #-}


module _ where
  open Indexed-coproducts
  open Indexed-coproduct
  open Indexed-products
  open Indexed-product

  instance
    Indexed-coproducts-Fun : {Idx : Type ℓ} → Indexed-coproducts (λ ℓ → Type ℓ) Fun Idx
    Indexed-coproducts-Fun .∐ = Σₜ _
    Indexed-coproducts-Fun .has-ic .ι = _,_
    Indexed-coproducts-Fun .has-ic .has-is-ic .∐-match f (i , x) = f i x
    Indexed-coproducts-Fun .has-ic .has-is-ic .ι-commute {f} _ x = f _ x
    Indexed-coproducts-Fun .has-ic .has-is-ic .∐-unique _ p j (i , x) = p i j x

    Indexed-products-Fun : {Idx : Type ℓ} → Indexed-products (λ ℓ → Type ℓ) Fun Idx
    Indexed-products-Fun {Idx} .∏ B = (x : Idx) → B x
    Indexed-products-Fun .has-ip .π i f = f i
    Indexed-products-Fun .has-ip .has-is-ip .∏-tuple f y i = f i y
    Indexed-products-Fun .has-ip .has-is-ip .π-commute {f} _ = f _
    Indexed-products-Fun .has-ip .has-is-ip .∏-unique _ g j y i = g i j y
{-# INCOHERENT Indexed-coproducts-Fun Indexed-products-Fun #-}

_ : (Idx : Type ℓi) → (Idx → Type ℓf) → 𝒰 (ℓi l⊔ ℓf)
_ = Σₜ

Πₜ : (Idx : Type ℓi) → (Idx → Type ℓf) → 𝒰 (ℓi l⊔ ℓf)
Πₜ _ = ∏ ⦃ _ ⦄ ⦃ Indexed-products-Fun ⦄
{-# INLINE Πₜ #-}


-- basic combinators for Π-types

flip : {C : A → B → Type ℓc} → (∀ a b → C a b) → (∀ b a → C a b)
flip f b a = f a b
{-# INLINE flip #-}

const : A → @0 B → A
const x _ = x
{-# INLINE const #-}

infixr -1 _$_
_$_ : {B : A → Type ℓb} (f : (a : A) → B a) (x : A) → B x
f $ a = f a
{-# INLINE _$_ #-}

infixl -1 _&_
_&_ : {B : A → Type ℓb} (x : A) (f : (a : A) → B a) → B x
a & f = f a
{-# INLINE _&_ #-}

infixr 9 _∘ᵈ_
_∘ᵈ_ : {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
       (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a)
       (x : A)
     → C x (f x)
(g ∘ᵈ f) x = g (f x)
{-# INLINE _∘ᵈ_ #-}


-- basic combinators for Σ-types

bimap : {B : A → Type ℓb} {P : A → Type ℓ} {Q : ∀ {a} → P a → B a → Type ℓ′}
      → (f : (a : A) → B a)
      → (∀ {a} (b : P a) → Q b (f a))
      → (p : Σₜ A P)
      → Σₜ (B (p .fst)) (Q (p .snd))
bimap f g (x , y) = f x , g y
{-# INLINE bimap #-}

first : {B : A → Type ℓb} {C : A → Type ℓc}
      → (f : (a : A) → B a)
      → (p : Σₜ A C) → B (p .fst) × C (p .fst)
first f = bimap f (λ x → x)
{-# INLINE first #-}

second : {B : A → Type ℓb} {C : A → Type ℓc}
       → (∀ {x} → B x → C x) → Σₜ A B → Σₜ A C
second f = bimap (λ x → x) f
{-# INLINE second #-}

module _ {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) (b : B a) → Type ℓc} where
  uncurry : (f : (a : A) (b : B a) → C a b)
            (p : Σₜ A B)
          → C (p .fst) (p .snd)
  uncurry f (x , y) = f x y
  {-# INLINE uncurry #-}

  curry : (f : (p : Σₜ A B) → C (p .fst) (p .snd))
          (x : A) (y : B x) → C x y
  curry f x y = f (x , y)
  {-# INLINE curry #-}
