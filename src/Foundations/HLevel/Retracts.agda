{-# OPTIONS --safe #-}
module Foundations.HLevel.Retracts where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.HLevel.Base
open import Foundations.Path.Groupoid
open import Foundations.Sigma.Properties

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A B C : Type ℓ

retract→is-contr : (f : A → B) (g : B → A)
                 → f is-left-inverse-of g
                 → is-contr A
                 → is-contr B
retract→is-contr f g h isC .fst = f (isC .fst)
retract→is-contr f g h isC .snd x =
  f (isC .fst) ＝⟨ ap f (isC .snd _) ⟩
  f (g x)      ＝⟨ h _ ⟩
  x            ∎

retract→is-prop : (f : A → B) (g : B → A)
                → f is-left-inverse-of g
                → is-prop A
                → is-prop B
retract→is-prop f g h propA x y =
  x       ＝⟨ sym (h _) ⟩
  f (g x) ＝⟨ ap f (propA _ _) ⟩
  f (g y) ＝⟨ h _ ⟩
  y       ∎

retract→is-of-hlevel : (n : HLevel) (f : A → B) (g : B → A)
                     → f is-left-inverse-of g
                     → is-of-hlevel n A
                     → is-of-hlevel n B
retract→is-of-hlevel 0 = retract→is-contr
retract→is-of-hlevel (suc 0) = retract→is-prop
retract→is-of-hlevel (suc (suc h)) f g p hlevel x y =
  retract→is-of-hlevel (suc h) sect (ap g) inv (hlevel (g x) (g y))
  where
    sect : g x ＝ g y → x ＝ y
    sect path =
      x       ＝⟨ sym (p _) ⟩
      f (g x) ＝⟨ ap f path ⟩
      f (g y) ＝⟨ p _ ⟩
      y       ∎

    inv : sect is-left-inverse-of (ap g)
    inv path =
      sym (p x) ∙ ap f (ap g path) ∙ p y ∙ refl ＝⟨ ap (λ e → sym (p _) ∙ _ ∙ e) (∙-id-r (p _)) ⟩
      sym (p x) ∙ ap f (ap g path) ∙ p y        ＝⟨ ap₂ _∙_ refl (sym (homotopy-natural p _)) ⟩
      sym (p x) ∙ p x ∙ path                    ＝⟨ ∙-assoc _ _ _ ⟩
      (sym (p x) ∙ p x) ∙ path                  ＝⟨ ap₂ _∙_ (∙-inv-l (p x)) refl ⟩
      refl ∙ path                               ＝⟨ ∙-id-l path ⟩
      path                                      ∎

is-iso→is-of-hlevel : (h : HLevel) (f : A → B) → is-iso f → is-of-hlevel h A → is-of-hlevel h B
is-iso→is-of-hlevel h f is-iso = retract→is-of-hlevel h f (is-iso .is-iso.inv) (is-iso .is-iso.rinv)

is-equiv→is-of-hlevel : (h : HLevel) (f : A → B) → is-equiv f → is-of-hlevel h A → is-of-hlevel h B
is-equiv→is-of-hlevel h f eqv = is-iso→is-of-hlevel h f (is-equiv→is-iso eqv)

is-of-hlevel-≃ : (h : HLevel) → (B ≃ A) → is-of-hlevel h A → is-of-hlevel h B
is-of-hlevel-≃ h f = is-iso→is-of-hlevel h from (iso to η ε) where open Equiv f

iso→is-of-hlevel : (h : HLevel) → Iso B A → is-of-hlevel h A → is-of-hlevel h B
iso→is-of-hlevel h (f , isic) = is-iso→is-of-hlevel h (isic .is-iso.inv) $
  iso f (isic .is-iso.linv) (isic .is-iso.rinv)

Π-is-of-hlevel : {B : A → Type ℓ′} (h : HLevel)
                 (Bhl : Π[ x ꞉ A ] is-of-hlevel h (B x))
               → is-of-hlevel h (Π[ x ꞉ A ] B x)
Π-is-of-hlevel 0 bhl = (λ _ → bhl _ .fst) , λ x i a → bhl _ .snd (x a) i
Π-is-of-hlevel 1 bhl f g i a = bhl a (f a) (g a) i
Π-is-of-hlevel (suc (suc h)) bhl f g =
  retract→is-of-hlevel (suc h) fun-ext happly (λ x → refl)
    (Π-is-of-hlevel (suc h) λ x → bhl x (f x) (g x))

Π-is-of-hlevel-implicit : {B : A → Type ℓ′} (h : HLevel)
                          (Bhl : (x : A) → is-of-hlevel h (B x))
                        → is-of-hlevel h ({x : A} → B x)
Π-is-of-hlevel-implicit h bhl = retract→is-of-hlevel h
  (λ f {x} → f x) (λ f x → f) (λ _ → refl)
  (Π-is-of-hlevel h bhl)

Π₂-is-of-hlevel
  : {B : A → Type ℓ′} {C : ∀ a → B a → Type ℓ″}
  → (n : HLevel) (Bhl : (x : A) (y : B x) → is-of-hlevel n (C x y))
  → is-of-hlevel n (∀ x y → C x y)
Π₂-is-of-hlevel n w = Π-is-of-hlevel n λ _ → Π-is-of-hlevel n (w _)

Π₃-is-of-hlevel
  : {B : A → Type ℓ′} {C : ∀ a → B a → Type ℓ″} {D : ∀ a b → C a b → Type ℓ‴}
  → (n : HLevel) (Bhl : (x : A) (y : B x) (z : C x y) → is-of-hlevel n (D x y z))
  → is-of-hlevel n (∀ x y z → D x y z)
Π₃-is-of-hlevel n w = Π-is-of-hlevel n λ _ → Π₂-is-of-hlevel n (w _)

fun-is-of-hlevel
  : {B : Type ℓ′}
  → (n : HLevel) → is-of-hlevel n B
  → is-of-hlevel n (A → B)
fun-is-of-hlevel n hl = Π-is-of-hlevel n (λ _ → hl)

Σ-is-of-hlevel : {B : A → Type ℓ′} (n : HLevel)
               → is-of-hlevel n A
               → ((x : A) → is-of-hlevel n (B x))
               → is-of-hlevel n (Σ A B)
Σ-is-of-hlevel 0 acontr bcontr =
  (acontr .fst , bcontr _ .fst) ,
    λ x → Σ-pathP (acontr .snd _)
                  (is-prop→pathP (λ _ → is-contr→is-prop (bcontr _)) _ _)
Σ-is-of-hlevel 1 aprop bprop (a , b) (a' , b') i =
  (aprop a a' i) , (is-prop→pathP (λ i → bprop (aprop a a' i)) b b' i)
Σ-is-of-hlevel {B} (suc (suc n)) h1 h2 x y =
  is-iso→is-of-hlevel (suc n)
    (is-iso-inv (Σ-path-iso .snd) .is-iso.inv)
    (Σ-path-iso .snd)
    (Σ-is-of-hlevel (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)

×-is-of-hlevel : {B : Type ℓ′}
               → (n : HLevel)
               → is-of-hlevel n A → is-of-hlevel n B
               → is-of-hlevel n (A × B)
×-is-of-hlevel n ahl bhl = Σ-is-of-hlevel n ahl (λ _ → bhl)

Lift-is-of-hlevel : (n : HLevel)
                  → is-of-hlevel n A
                  → is-of-hlevel n (Lift ℓ′ A)
Lift-is-of-hlevel n a-hl = retract→is-of-hlevel n lift lower (λ _ → refl) a-hl

≃-is-of-hlevel : (n : ℕ) → is-of-hlevel n A → is-of-hlevel n B → is-of-hlevel n (A ≃ B)
≃-is-of-hlevel {A} {B} zero Ahl Bhl = e , deform where
  e : A ≃ B
  e = (λ _ → Bhl .fst) , is-contr→is-equiv Ahl Bhl

  deform : (e′ : A ≃ B) → e ＝ e′
  deform (g , _) = Σ-path (λ i x → Bhl .snd (g x) i)
                          (is-equiv-is-prop _ _ _)

≃-is-of-hlevel (suc n) _ Bhl =
  Σ-is-of-hlevel (suc n)
    (fun-is-of-hlevel (suc n) Bhl)
    λ f → is-prop→is-hlevel-suc (is-equiv-is-prop f)

≃-is-of-hlevel-left-suc : (n : ℕ) → is-of-hlevel (suc n) A → is-of-hlevel (suc n) (A ≃ B)
≃-is-of-hlevel-left-suc zero    A-hl e =
  ≃-is-of-hlevel 1 A-hl (retract→is-prop to from ε A-hl) e
  where open Equiv e
≃-is-of-hlevel-left-suc (suc n) A-hl e =
  ≃-is-of-hlevel (suc (suc n)) A-hl (is-of-hlevel-≃ (suc (suc n)) (e ₑ⁻¹) A-hl) e

≃-is-of-hlevel-right-suc : (n : ℕ) → is-of-hlevel (suc n) B → is-of-hlevel (suc n) (A ≃ B)
≃-is-of-hlevel-right-suc zero    B-hl e =
  ≃-is-of-hlevel 1 (retract→is-prop from to η B-hl) B-hl e
  where open Equiv e
≃-is-of-hlevel-right-suc (suc n) B-hl e =
  ≃-is-of-hlevel (suc (suc n)) (is-of-hlevel-≃ (suc (suc n)) e B-hl) B-hl e
