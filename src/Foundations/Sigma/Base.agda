{-# OPTIONS --safe #-}
module Foundations.Sigma.Base where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Notation.Logic
open import Foundations.Notation.Underlying

open import Agda.Builtin.Sigma public

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ ℓᵉ ℓᶠ : Level
  A : Type ℓᵃ
  B : A → Type ℓᵇ

infixr 8 _×ₜ_
_×ₜ_ : (A : Type ℓ) (B : Type ℓ′) → Type (ℓ ⊔ ℓ′)
A ×ₜ B = Σ A λ _ → B

instance
  Σ-Type : {A : Type ℓ} ⦃ u : Underlying A ⦄
         → Σ-notation A (𝒰 ℓ′) (𝒰 (u .ℓ-underlying ⊔ ℓ′))
  Σ-Type .Σ-notation.Σ X = Σ ⌞ X ⌟⁰

  ×-Type : ×-notation (Type ℓ) (Type ℓ′) (Type (ℓ ⊔ ℓ′))
  ×-Type ._×_ = _×ₜ_

  Underlying-Σ : ⦃ ua : Underlying A ⦄ → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟⁰ x = ⌞ x .fst ⌟⁰

<_,_> : {C : ∀ {a} → B a → Type ℓᶜ}
      → (f : (x : A) → B x)
      → ((x : A) → C (f x))
      → ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

bimap : {P : A → Type ℓ} {Q : ∀ {a} → P a → B a → Type ℓ′}
      → (f : (a : A) → B a)
      → (∀ {a} (b : P a) → Q b (f a))
      → ((a , b) : Σ A P)
      → Σ (B a) (Q b)
bimap f g (x , y) = f x , g y

bimapˢ : {B : Type ℓᵇ} {P : A → Type ℓ} {Q : B → Type ℓ′}
       → (f : A → B)
       → (∀ {x} → P x → Q (f x))
       → Σ A P → Σ B Q
bimapˢ = bimap

first : {B : A → Type ℓᵇ} {C : A → Type ℓᶜ} → (f : (a : A) → B a) → ((a , _) : Σ A C) → B a × C a
first f = bimap f (λ x → x)

second : {C : A → Type ℓᶜ} → (∀ {x} → B x → C x) → Σ A B → Σ A C
second f = bimap (λ x → x) f


-- note that `curry¹` is just `_$_` again

-- TODO: automate this to get `curryⁿ` and `uncurryⁿ` (`_$ⁿ_`)
module _ {A : Type ℓᵃ} {B : A → Type ℓᵇ} {C : (a : A) (b : B a) → Type ℓᶜ} where

  _$²_ : (f : (a : A) (b : B a) → C a b)
         (p : Σ[ x ꞉ A ] B x)
       → C (fst p) (snd p)
  f $² (x , y) = f x y

  curry² : (f : (p : Σ[ a ꞉ A ] B a) → C (p .fst) (p .snd))
           (x : A) (y : B x) → C x y
  curry² f x y = f (x , y)

  module _ {D : (a : A) (b : B a) (c : C a b) → Type ℓᵈ} where
    _$³_ : (f : (a : A) (b : B a) (c : C a b) → D a b c)
           (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] C x y)
         → D (p .fst) (p .snd .fst) (p .snd .snd)
    f $³ (x , y , z) = f x y z

    curry³ : (f : (p : Σ[ a ꞉ A ] Σ[ b ꞉ B a ] C a b) → D (p .fst) (p .snd .fst) (p .snd .snd))
             (x : A) (y : B x) (z : C x y) → D x y z
    curry³ f x y z = f (x , y , z)

    module _ {E : (a : A) (b : B a) (c : C a b) (d : D a b c) → Type ℓᵉ} where
      _$⁴_ : (f : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d)
             (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] Σ[ z ꞉ C x y ] D x y z)
           → E (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd)
      f $⁴ (x , y , z , w) = f x y z w

      _$⁵_ : {F : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → Type ℓᶠ}
             (f : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → F a b c d e)
             (p : Σ[ x ꞉ A ] Σ[ y ꞉ B x ] Σ[ z ꞉ C x y ] Σ[ w ꞉ D x y z ] E x y z w)
           → F (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd .fst) (p .snd .snd .snd .snd)
      f $⁵ (x , y , z , w , u) = f x y z w u


fibreᴱ : {A  : Type ℓᵃ} {@0 B : Type ℓᵇ} (f : A → B) (@0 y : B) → Type _
fibreᴱ {A} f y = Σ[ x ꞉ A ] Erased (f x ＝ y)
