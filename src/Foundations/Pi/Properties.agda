{-# OPTIONS --safe #-}
module Foundations.Pi.Properties where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Transport

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A B C D : Type ℓ
  P Q : A → Type ℓ′

Π-cod-≃ : Π[ x ꞉ A ] (P x ≃ Q x)
        → Π[ x ꞉ A ] P x
        ≃ Π[ x ꞉ A ] Q x
Π-cod-≃ k .fst f x = k x .fst (f x)
Π-cod-≃ k .snd .equiv-proof f .fst .fst x   = equiv-centre (k x) (f x) .fst
Π-cod-≃ k .snd .equiv-proof f .fst .snd i x = equiv-centre (k x) (f x) .snd i
Π-cod-≃ k .snd .equiv-proof f .snd (g , p) i .fst x =
  equiv-path (k x) (f x) (g x , λ j → p j x) i .fst
Π-cod-≃ k .snd .equiv-proof f .snd (g , p) i .snd j x =
  equiv-path (k x) (f x) (g x , λ k → p k x) i .snd j

Π-dom-≃ : {A : Type ℓ} {B : Type ℓ′} {P : A → Type ℓ″}
          (e : B ≃ A)
        → Π[ x ꞉ A ] P x
        ≃ Π[ x ꞉ B ] P (e $ x)
Π-dom-≃ {A} {B} {P} e = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  module e = Equiv e
  to : Π[ x ꞉ A ] P x → Π[ x ꞉ B ] P (e.to x)
  to k x = k (e.to x)

  from : Π[ x ꞉ B ] P (e.to x) → Π[ x ꞉ A ] P x
  from k x = subst P (e.ε # x) (k (e.from x))

  ri : from section-of′ to
  ri k = fun-ext λ x →
            ap² (subst P) (e.zig′ x ⁻¹) (from-pathᴾ⁻ (ap k (e.η # x ⁻¹)))
          ∙ transport⁻-transport (ap (P ∘ e.to) (e.η # x)) (k x)

  li : from retract-of′ to
  li k = fun-ext λ x →
      ap (subst P _) (from-pathᴾ⁻ (ap k (e.ε # x)))
    ∙ transport⁻-transport (ap P (e.ε # x) ⁻¹) _

Π-ap : {A : Type ℓ} {A′ : Type ℓ′} {P : A → Type ℓ″} {Q : A′ → Type ℓ‴}
       (e : A ≃ A′)
     → Π[ a ꞉ A ] (P a ≃ Q (e $ a))
     → Π[ x ꞉ A ] P x ≃ Π[ y ꞉ A′ ] Q y
Π-ap e e′ = Π-cod-≃ e′ ∙ Π-dom-≃ e ⁻¹

Π≃∀ : Π[ x ꞉ A ] P x
    ≃ ∀[ x ꞉ A ] P x
Π≃∀ .fst = implicit
Π≃∀ .snd .equiv-proof = strict-contr-fibres λ p _ → p

∀-cod-≃ : Π[ x ꞉ A ] (P x ≃ Q x)
        → ∀[ x ꞉ A ] P x
        ≃ ∀[ x ꞉ A ] Q x
∀-cod-≃ k = Π≃∀ ⁻¹ ∙ Π-cod-≃ k ∙ Π≃∀

function-≃ : (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)
function-≃ {A} {B} {C} {D} dom rng = ≅→≃ $ iso to from
  (fun-ext λ f → fun-ext λ x → rngi .Iso.inv-o # _  ∙ ap f (domi .Iso.inv-o # x))
  (fun-ext λ f → fun-ext λ x → rngi .Iso.inv-i # _  ∙ ap f (domi .Iso.inv-i # x))
  where
  rngi = ≃→≅ rng
  domi = ≃→≅ dom
  to : (A → C) → B → D
  to f b = rng $ f $ domi ⁻¹ $ b
  from : (B → D) → A → C
  from g a = rng ⁻¹ $ g $ domi $ a

fun-ext-≃
  : {A : Type ℓ} {B : Type ℓ′} {f g : A → B}
  → (f ＝ g) ≃ Π[ a ꞉ A ] (f a ＝ g a)
fun-ext-≃ .fst = happly
fun-ext-≃ .snd .equiv-proof = strict-contr-fibres fun-ext

fun-ext-dep
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′} {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ( ∀ {x₀ x₁} (p : ＜ x₀ ／ A ＼ x₁ ＞) → ＜ f x₀ ／ (λ i → B i (p i)) ＼ g x₁ ＞ )
  → ＜ f ／ (λ i → Π[ x ꞉ A i ] B i x) ＼ g ＞
fun-ext-dep {A} {B} h i x = coei→1 (λ j → B i (coei→i A i x j)) (i ∨ ~ i) $
  h (λ j → coe A i j x) i

fun-ext-dep-≃
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
    {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}

  → ( {x₀ : A i0} {x₁ : A i1} (p : ＜ x₀ ／ A ＼ x₁ ＞)
    → ＜ f x₀ ／ (λ i → B i (p i)) ＼ g x₁ ＞ )
  ≃ ＜ f ／ (λ i → Π[ x ꞉ A i ] B i x) ＼ g ＞
fun-ext-dep-≃ {A} {B} {f} {g} = ≅→≃ $ iso fun-ext-dep (λ q p i → q i (p i))
  (λ m q i x → coei→1 (λ k → B i (coei→i A i x (k ∨ m))) (m ∨ ∂ i) $
    q i $ coei→i A i x m)
  (λ m h p i → coei→1 (λ k → B i (coei→i A i (p i) (m ∨ k))) (m ∨ ∂ i) $
    h (λ j → coe-path A (λ i → p i) i j m) i)

Π-contract-dom : {A : Type ℓ} {P : A → Type ℓ′}
                 (A-c : is-contr A)
               → Π[ x ꞉ A ] P x ≃ P (centre A-c)
Π-contract-dom {A} {P} A-c = ≅→≃ $ iso (λ f → f $ centre A-c) (λ p x → subst P (paths A-c x) p)
  (fun-ext λ p → ap (λ φ → transport (ap P φ) p) (is-contr→is-set A-c _ _ _ _) ∙ transport-refl _)
  (fun-ext λ f → fun-ext λ x → from-pathᴾ $ ap f (paths A-c x))

-- TODO opaque proofs of invertibility?
hetero-homotopy≃homotopy
  : {A : I → Type ℓ} {B : (i : I) → Type ℓ′}
    {f : A i0 → B i0} {g : A i1 → B i1}
  → ({x₀ : A i0} {x₁ : A i1} → ＜ x₀ ／ A ＼ x₁ ＞ → ＜ f x₀ ／ B ＼ g x₁ ＞)
  ≃ (Π[ x₀ ꞉ A i0 ] ＜ f x₀ ／ B ＼ g (coe0→1 A x₀) ＞)
hetero-homotopy≃homotopy {A} {B} {f} {g} = ≅→≃ isom where
  c : {x₀ : A i0} → is-contr (Singletonᴾ A x₀)
  c {x₀} = singletonᴾ-is-contr A x₀

  open Iso

  isom : ({x₀ : A i0} {x₁ : A i1} → ＜ x₀ ／ A ＼ x₁ ＞ → ＜ f x₀ ／ B ＼ g x₁ ＞)
       ≅ (Π[ x₀ ꞉ A i0 ] ＜ f x₀ ／ B ＼ g (coe0→1 A x₀) ＞)
  isom .to h x₀ = h $ c .fst .snd
  isom .from k {x₀} {x₁} p =
    subst (λ fib → ＜ f x₀ ／ B ＼ g (fib .fst) ＞) (c .snd (x₁ , p)) (k x₀)
  isom .inverses .Inverses.inv-o = fun-ext λ k → fun-ext λ x₀
    → ap (λ α → subst (λ fib → ＜ f x₀ ／ B ＼ g (fib .fst) ＞) α (k x₀))
      (is-contr→is-set c (c .fst) (c .fst) (c .snd $ c .fst) refl)
    ∙ transport-refl (k x₀)
  isom .inverses .Inverses.inv-i j h {x₀} {x₁} p =
    coei→1 (λ i → ＜ f x₀ ／ B ＼ g (c .snd (x₁ , p) (i ∨ j) .fst) ＞)
      j
      (h $ c .snd (x₁ , p) j .snd)
