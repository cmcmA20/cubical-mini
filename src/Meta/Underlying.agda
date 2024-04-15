{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Prelude
  hiding (_$_)

open import Meta.Reflection.Base

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.List.Instances.FromProduct
open import Data.Nat.Base

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟⁰         : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public

{-# DISPLAY Underlying.⌞_⌟⁰ f x = ⌞ x ⌟⁰ #-}

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : A → Type ℓ′
  P : Type ℓ′

instance
  Underlying-Σ : ⦃ ua : Underlying A ⦄ → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟⁰ x = ⌞ x .fst ⌟⁰

  Underlying-Type : Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟⁰ x = x

  Underlying-Lift : ⦃ ua : Underlying A ⦄ → Underlying (Lift ℓ′ A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟⁰ x = ⌞ x .lower ⌟⁰


data Modality′ : Type where
  cirr rirr ur : Modality′
  -- ^ compiletime irrelevant
  --   runtime irrelevant
  --   unrestricted

MFun : (m : Modality′) {ℓ ℓ′ : Level} (A : Type ℓ) (B : Type ℓ′) → Type (ℓ ⊔ ℓ′)
MFun cirr A B = @irr A → B
MFun rirr A B = @0   A → B
MFun ur   A B =      A → B

MApp : (m : Modality′) {ℓ ℓ′ : Level} (A : Type ℓ) (B : MFun m A (Type ℓ′)) → Type (ℓ ⊔ ℓ′)
MApp cirr A B = (@irr x : A) → B x
MApp rirr A B = (@0   x : A) → B x
MApp ur   A B = (     x : A) → B x

-- Notation class for type families which are "function-like"
-- Looks like it's dependent now
record
  Funlike (m : Modality′) {ℓ ℓ′ ℓ″}
    (A : Type ℓ) (Arg : Type ℓ′) (F : MFun m Arg (Type ℓ″)) : Type (ℓ ⊔ ℓ′ ⊔ ℓ″) where
  infixl 999 _#_
  field _#_ : A → MApp m Arg F

  infixr -1 _$_
  _$_ = _#_

open Funlike ⦃ ... ⦄ public
{-# DISPLAY Funlike._#_ p f x = f # x #-}

ap$
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike ur F A B ⦄
  → (f : F) {x y : A} (p : x ＝ y)
  → ＜ f $ x ／ (λ i → B (p i)) ＼ f $ y ＞
ap$ f = ap (f $_)

-- Generalised happly.
_$ₚ_
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike ur F A B ⦄
  → {f g : F} → f ＝ g → (x : A) → f # x ＝ g # x
f $ₚ x = ap² _$_ f refl

instance
  Funlike-Erased-≃ : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (A ≃ᴱ B) A (λ _ → B)
  Funlike-Erased-≃ ._#_ = fst

  Funlike-≃ : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (A ≃ B) A (λ _ → B)
  Funlike-≃ ._#_ = fst

  Funlike-Iso : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (Iso A B) A (λ _ → B)
  Funlike-Iso ._#_ = fst

  Funlike-Irr-Π : {A : Type ℓ} {B : @irr A → Type ℓ′} → Funlike cirr ((@irr a : A) → B a) A B
  Funlike-Irr-Π ._#_ = id

  Funlike-Erased-Π : {@0 A : Type ℓ} {B : @0 A → Type ℓ′} → Funlike rirr ((@0 a : A) → B a) A B
  Funlike-Erased-Π ._#_ = id

  Funlike-Π : {A : Type ℓ} {B : A → Type ℓ′} → Funlike ur ((a : A) → B a) A B
  Funlike-Π ._#_ = id

  Funlike-Homotopy
    : {A : Type ℓ} {B : A → Type ℓ′} {f g : ∀ x → B x}
    → Funlike ur (f ＝ g) A (λ x → f x ＝ g x)
  Funlike-Homotopy ._#_ = happly


-- Generalised "sections" (e.g. of a presheaf) notation.
infix 999 _ʻ_
_ʻ_
  : {A : Type ℓ} {B : A → Type ℓ′} {F : Type ℓ″}
  → ⦃ _ : Funlike ur F A B ⦄
  → F → (x : A) → ⦃ _ : Underlying (B x) ⦄
  → Type _
F ʻ x = ⌞ F $ x ⌟⁰


infixr 6 Σ-syntax-und
Σ-syntax-und
  : ⦃ _ : Underlying A ⦄ (X : A) (F : ⌞ X ⌟⁰ → Type ℓ′)
  → Type _
Σ-syntax-und X F = Σ ⌞ X ⌟⁰ F
syntax Σ-syntax-und X (λ x → F) = Σ[ x ꞉ X ] F
{-# DISPLAY Σ-syntax-und = Σ #-}

infixr 6 Π-syntax-und
Π-syntax-und
  : ⦃ _ : Underlying A ⦄ (X : A) (F : ⌞ X ⌟⁰ → Type ℓ′)
  → Type _
Π-syntax-und X F = (x : ⌞ X ⌟⁰) → F x
syntax Π-syntax-und X (λ x → F) = Π[ x ꞉ X ] F

infixr 6 ∀-syntax-und
∀-syntax-und
  : ⦃ _ : Underlying A ⦄ (X : A) (F : ⌞ X ⌟⁰ → Type ℓ′)
  → Type _
∀-syntax-und X F = {x : ⌞ X ⌟⁰} → F x
syntax ∀-syntax-und X (λ x → F) = ∀[ x ꞉ X ] F
