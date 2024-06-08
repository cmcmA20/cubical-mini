{-# OPTIONS --safe #-}
module Foundations.Pi.Properties where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Transport

private variable
  ℓ ℓ′ : Level
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

Π-dom-≃ : (e : B ≃ A)
        → Π[ x ꞉ A ] P x
        ≃ Π[ x ꞉ B ] P (e .fst x)
Π-dom-≃ {B} {A} {P} e = ≅→≃ $ to , iso from ri li where
  module e = Equiv e
  to : Π[ x ꞉ A ] P x → Π[ x ꞉ B ] P (e.to x)
  to k x = k (e.to x)

  from : Π[ x ꞉ B ] P (e.to x) → Π[ x ꞉ A ] P x
  from k x = substₚ P (e.ε x) (k (e.from x))

  ri : from is-right-inverse-of to
  ri k = fun-ext λ x →
           ap² (substₚ P) (e.zig x ⁻¹)
            (from-pathᴾ (symᴾ-from-goal (ap k (e.η x))) ⁻¹)
          ∙ transport⁻-transport (ap P (ap e.to (e.η x ⁻¹))) (k x)

  li : from is-left-inverse-of to
  li k = fun-ext λ x →
           ap (substₚ P _) (from-pathᴾ (symᴾ-from-goal (ap k (e.ε x))) ⁻¹)
         ∙ transport⁻-transport (ap P (e.ε x) ⁻¹) _

Π≃∀ : Π[ x ꞉ A ] P x
    ≃ ∀[ x ꞉ A ] P x
Π≃∀ .fst = implicit
Π≃∀ .snd .equiv-proof = strict-contr-fibres λ p _ → p

∀-cod-≃ : Π[ x ꞉ A ] (P x ≃ Q x)
        → ∀[ x ꞉ A ] P x
        ≃ ∀[ x ꞉ A ] Q x
∀-cod-≃ k = Π≃∀ ⁻¹ ∙ Π-cod-≃ k ∙ Π≃∀

function-≃ : (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)
function-≃ dom rng = ≅→≃ the-iso where
  rng-iso = is-equiv→is-iso (rng .snd)
  dom-iso = is-equiv→is-iso (dom .snd)

  the-iso : Iso _ _
  the-iso .fst f x = rng .fst (f (dom-iso .is-iso.inv x))
  the-iso .snd .is-iso.inv f x = rng-iso .is-iso.inv (f (dom .fst x))
  the-iso .snd .is-iso.rinv f =
    fun-ext λ x → rng-iso .is-iso.rinv _
                ∙ ap f (dom-iso .is-iso.rinv _)
  the-iso .snd .is-iso.linv f =
    fun-ext λ x → rng-iso .is-iso.linv _
                ∙ ap f (dom-iso .is-iso.linv _)

fun-ext-≃
  : {f g : A → B}
  → (f ＝ g) ≃ Π[ a ꞉ A ] (f a ＝ g a)
fun-ext-≃ .fst = happly
fun-ext-≃ .snd .equiv-proof = strict-contr-fibres fun-ext

fun-ext-dep
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′} →  ∀ {f g}
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
fun-ext-dep-≃ {A} {B} {f} {g} = ≅→≃ isom where
  open is-iso
  isom : Iso _ _
  isom .fst = fun-ext-dep
  isom .snd .is-iso.inv q p i = q i (p i)

  isom .snd .rinv q m i x =
    coei→1 (λ k → B i (coei→i A i x (k ∨ m))) (m ∨ ∂ i) $
      q i (coei→i A i x m)

  isom .snd .linv h m p i =
    coei→1 (λ k → B i (lemi→i m k)) (m ∨ ∂ i) $ h (λ j → lemi→j j m) i
    where
      lemi→j : ∀ j → coe A i j (p i) ＝ p j
      lemi→j j k = coe-path A (λ i → p i) i j k

      lemi→i : ＜ coei→i A i (p i) ／ (λ m → lemi→j i m ＝ p i) ＼ refl ＞
      lemi→i m k = coei→i A i (p i) (m ∨ k)

-- TODO opaque proofs of invertibility?
hetero-homotopy≃homotopy
  : {A : I → Type ℓ} {B : (i : I) → Type ℓ′}
    {f : A i0 → B i0} {g : A i1 → B i1}
  → ({x₀ : A i0} {x₁ : A i1} → ＜ x₀ ／ A ＼ x₁ ＞ → ＜ f x₀ ／ B ＼ g x₁ ＞)
  ≃ (Π[ x₀ ꞉ A i0 ] ＜ f x₀ ／ B ＼ g (coe0→1 A x₀) ＞)
hetero-homotopy≃homotopy {A} {B} {f} {g} = ≅→≃ isom where
  open is-iso
  c : {x₀ : A i0} → is-contr (Singletonᴾ A x₀)
  c {x₀} = singletonᴾ-is-contr A x₀

  isom : ({x₀ : A i0} {x₁ : A i1} → ＜ x₀ ／ A ＼ x₁ ＞ → ＜ f x₀ ／ B ＼ g x₁ ＞)
       ≅ (Π[ x₀ ꞉ A i0 ] ＜ f x₀ ／ B ＼ g (coe0→1 A x₀) ＞)
  isom .fst h x₀ = h $ c .fst .snd
  isom .snd .inv k {x₀} {x₁} p =
    substₚ (λ fib → ＜ f x₀ ／ B ＼ g (fib .fst) ＞) (c .snd (x₁ , p)) (k x₀)

  isom .snd .rinv k = fun-ext λ x₀ →
    ap (λ α → substₚ (λ fib → ＜ f x₀ ／ B ＼ g (fib .fst) ＞) α (k x₀))
      (is-contr→is-set c (c .fst) (c .fst) (c .snd $ c .fst) refl)
    ∙ transport-refl (k x₀)

  isom .snd .linv h j {x₀} {x₁} p =
    coei→1
      (λ i → ＜ f x₀ ／ B ＼ g (c .snd (x₁ , p) (i ∨ j) .fst) ＞)
      j $ h $ c .snd (x₁ , p) j .snd
