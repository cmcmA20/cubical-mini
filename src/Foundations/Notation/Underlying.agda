{-# OPTIONS --safe #-}
module Foundations.Notation.Underlying where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Agda.Builtin.Sigma

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public

{-# DISPLAY Underlying.⌞_⌟ f x = ⌞ x ⌟ #-}

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : A → Type ℓ′
  P : Type ℓ′

instance
  Underlying-Type : Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟ x = x

  Underlying-Lift : ⦃ ua : Underlying A ⦄ → Underlying (Lift ℓ′ A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .lower ⌟


data Modality′ : Type where
  cirr rirr ur : Modality′
  -- ^ compiletime irrelevant
  --   runtime irrelevant
  --   unrestricted

MFun : (m : Modality′) {ℓ ℓ′ : Level} (A : Type ℓ) (B : Type ℓ′) → Type (ℓ ⊔ ℓ′)
MFun cirr A B = @irr A → B
MFun rirr A B = @0   A → B
MFun ur   A B =      A → B

MPi : (m : Modality′) {ℓ ℓ′ : Level} (A : Type ℓ) (B : MFun m A (Type ℓ′)) → Type (ℓ ⊔ ℓ′)
MPi cirr A B = (@irr x : A) → B x
MPi rirr A B = (@0   x : A) → B x
MPi ur   A B = (     x : A) → B x

private
  mapply′
    : {m : Modality′} {A : Type ℓ} {Arg : Type ℓ′} {Z : Type ℓ″}
    → A → MFun m (Σ A λ _ → Arg) Z → MFun m Arg Z
  mapply′ {m = cirr} a f ar = f (a , ar)
  mapply′ {m = rirr} a f ar = f (a , ar)
  mapply′ {m = ur}   a f ar = f (a , ar)


-- Notation class for type families which are "function-like"
record
  Funlike (m : Modality′) {ℓ ℓ′ ℓ″}
    (A : Type ℓ) (Arg : Type ℓ′) (F : MFun m (Σ A λ _ → Arg) (Type ℓ″)) : Type (ℓ ⊔ ℓ′ ⊔ ℓ″) where
  infixl 999 _#_
  field _#_ : (a : A) → MPi m Arg (mapply′ a F)

  infixr -1 _$_
  _$_ = _#_

open Funlike ⦃ ... ⦄ public
{-# DISPLAY Funlike._#_ p f x = f # x #-}

ap$
  : {A : Type ℓ} {F : Type ℓ′} {B : (Σ F λ _ → A) → Type ℓ″}
  → ⦃ _ : Funlike ur F A B ⦄
  → (f : F) {x y : A} (p : x ＝ y)
  → ＜ f # x ／ (λ i → B (f , p i)) ＼ f # y ＞
ap$ f = ap (f $_)

-- Generalised happly.
infixr -1 _$ₚ_
_$ₚ_
  : {A : Type ℓ} {F : Type ℓ′} {B : (Σ F λ _ → A) → Type ℓ″}
  → ⦃ _ : Funlike ur F A B ⦄
  → {f g : F} (p : f ＝ g) (x : A) → ＜ f # x ／ (λ i → B (p i , x)) ＼ g # x ＞
_$ₚ_ p x i = p i # x

infixl 999 _#ₚ_
_#ₚ_ = _$ₚ_

instance
  Funlike-Irr-Π₀ : {A : Type ℓ} {B : @irr A → Type ℓ′} → Funlike cirr ((@irr a : A) → B a) A λ z → B (z .snd)
  Funlike-Irr-Π₀ ._#_ f = f

  Funlike-Erased-Π₀ : {@0 A : Type ℓ} {B : @0 A → Type ℓ′} → Funlike rirr ((@0 a : A) → B a) A λ z → B (z .snd)
  Funlike-Erased-Π₀ ._#_ f = f

  Funlike-Erased-Π₁
    : {@0 A : Type ℓ} {B : @0 A → Type ℓ′} {x y : A}
    → Funlike rirr (MPi rirr A B) (x ＝ y) λ (f , p) → ＜ f x ／ (λ i → B (p i)) ＼ f y ＞
  Funlike-Erased-Π₁ ._#_ f p i = f (p i)
  {-# INCOHERENT Funlike-Erased-Π₁ #-}

  Funlike-Π₀ : {A : Type ℓ} {B : A → Type ℓ′} → Funlike ur ((a : A) → B a) A λ z → B (z .snd)
  Funlike-Π₀ ._#_ f = f

  Funlike-Π₁
    : {A : Type ℓ} {B : A → Type ℓ′} {x y : A}
    → Funlike ur (MPi ur A B) (x ＝ y) λ (f , p) → ＜ f x ／ (λ i → B (p i)) ＼ f y ＞
  Funlike-Π₁ ._#_ f p i = f (p i)
  {-# INCOHERENT Funlike-Π₁ #-}

  Funlike-Homotopy
    : {A : Type ℓ} {B : A → Type ℓ′} {f g : ∀ x → B x}
    → Funlike ur (f ＝ g) A (λ z → f (z .snd) ＝ g (z .snd))
  Funlike-Homotopy ._#_ p x i = p i x

  Funlike-Σ
    : {X : Type ℓ} {B : Σ X (λ _ → A) → Type ℓ′} {P : X → Type ℓ″}
    → ⦃ Funlike ur X A B ⦄
    → Funlike ur (Σ X P) A λ (w , z) → B (w .fst , z)
  Funlike-Σ ._#_ (f , _) = f #_
  {-# OVERLAPPABLE Funlike-Σ #-}


-- Generalised "sections" (e.g. of a presheaf) notation.
infix 999 _ʻ_
_ʻ_
  : {A : Type ℓ} {F : Type ℓ′} {B : (Σ F λ _ → A) → Type ℓ″}
  → ⦃ _ : Funlike ur F A B ⦄
  → (f : F) (x : A) ⦃ ub : Underlying (B (f , x)) ⦄
  → Type _
F ʻ x = ⌞ F $ x ⌟
