{-# OPTIONS --safe #-}
module Functions.Equiv.HalfAdjoint where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Path
open import Foundations.Sigma
open import Foundations.Transport
open import Foundations.Univalence.Base

open import Meta.Marker
open import Meta.Underlying

open import Functions.Fibration

private variable
  ℓ₁ ℓ₂ : Level
  A : Type ℓ₁
  B : Type ℓ₂
  f : A → B

is-half-adjoint-equiv : (f : A → B) → Type _
is-half-adjoint-equiv {A} {B} f =
  Σ[ g ꞉ (B → A) ]
  Σ[ η ꞉ g is-left-inverse-of f ]
  Σ[ ε ꞉ g is-right-inverse-of f ]
  Π[ x ꞉ A ] (ap f (η x) ＝ ε (f x))

is-iso→is-half-adjoint-equiv : is-iso f → is-half-adjoint-equiv f
is-iso→is-half-adjoint-equiv {f} iiso =
  g , η , ε′ , λ x → sym (zig x)
  where
    open is-iso iiso renaming (inv to g ; linv to η ; rinv to ε)
    ε′ : (y : _) → f (g y) ＝ y
    ε′ y = sym (ε (f (g y))) ∙ ap f (η (g y)) ∙ ε y

    zig : (x : _) → ε′ (f x) ＝ ap f (η x)
    zig x =
      ε′ (f x)                                                   ＝⟨⟩
      sym (ε (f (g (f x)))) ∙ ap f ⌜ η (g (f x)) ⌝ ∙ ε (f x)     ＝⟨ ap! (homotopy-invert η) ⟩
      sym (ε (f (g (f x)))) ∙ ⌜ ap (f ∘ g ∘ f) (η x) ∙ ε (f x) ⌝ ＝˘⟨ ap¡ (homotopy-natural ε _) ⟩
      sym (ε (f (g (f x)))) ∙ ε (f (g (f x))) ∙ ap f (η x)       ＝⟨ ∙-cancel-l (ε (f (g (f x)))) (ap f (η x)) ⟩
      ap f (η x)                                                 ∎


@0 is-half-adjoint-equiv→is-equiv : is-half-adjoint-equiv f → is-equiv f
is-half-adjoint-equiv→is-equiv {f} (g , η , ε , zig) .equiv-proof y = fib , contract where
  fib : fibre f y
  fib = g y , ε y

  fibre-paths′ : {z@(a , p) z′@(a′ , p′) : fibre f y}
               → z ＝ z′
               ≃ Σ[ q ꞉ a ＝ a′ ] (ap f q ∙ p′ ＝ p)
  fibre-paths′ = fibre-paths ∙ₑ Σ-ap-snd λ _ → flip-lₑ ∙ₑ sym-≃

  contract : (fib₂ : fibre f y) → fib ＝ fib₂
  contract (x , p) = (fibre-paths′ ₑ⁻¹) # (x=gy , path) where
    x=gy = ap g (sym p) ∙ η x

    path : ap f (ap g (sym p) ∙ η x) ∙ p ＝ ε y
    path =
      ⌜ ap f (ap g (sym p) ∙ η x) ⌝ ∙ p               ＝⟨ ap! (ap-comp-∙ f (ap g (sym p)) (η x)) ⟩
      (ap (f ∘ g) (sym p) ∙ ap f (η x)) ∙ p           ＝˘⟨ ∙-assoc _ _ _ ⟩
      ap (f ∘ g) (sym p) ∙ ⌜ ap f (η x) ⌝ ∙ p         ＝⟨ ap! (zig _) ⟩ -- by the triangle identity
      ap (f ∘ g) (sym p) ∙ ⌜ ε (f x) ∙ p ⌝            ＝⟨ ap! (homotopy-natural ε p)  ⟩ -- by naturality of ε
      ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ∙ ε y         ＝⟨ ∙-assoc _ _ _ ⟩
      ⌜ ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ⌝ ∙ ε y     ＝˘⟨ ap¡ (ap-comp-∙ (f ∘ g) (sym p) p) ⟩
      ap (f ∘ g) ⌜ sym p ∙ p ⌝ ∙ ε y                  ＝⟨ ap! (∙-inv-r _) ⟩
      ap (f ∘ g) refl ∙ ε y                           ＝⟨⟩
      refl ∙ ε y                                      ＝⟨ ∙-id-l (ε y) ⟩
      ε y                                             ∎

@0 is-iso→is-equiv′ : is-iso f → is-equiv f
is-iso→is-equiv′ = is-half-adjoint-equiv→is-equiv ∘ is-iso→is-half-adjoint-equiv

is-equiv→is-half-adjoint-equiv : is-equiv f → is-half-adjoint-equiv f
is-equiv→is-half-adjoint-equiv {f} eqv =
    is-equiv→inverse eqv
  , is-equiv→unit eqv
  , is-equiv→counit eqv
  , is-equiv→zig eqv
