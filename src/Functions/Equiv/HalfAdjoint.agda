{-# OPTIONS --safe #-}
module Functions.Equiv.HalfAdjoint where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Path.Groupoid
open import Foundations.Sigma
open import Foundations.Univalence.Base

open import Meta.Reflection.Marker

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

is-iso→is-half-adjoint-equiv
  : {f : A → B}
  → is-iso f → is-half-adjoint-equiv f
is-iso→is-half-adjoint-equiv {A} {B} {f} iiso =
  g , η , ε′ , λ x → sym (zig x)
  where
    open is-iso iiso renaming (inv to g ; linv to η ; rinv to ε)

    ε′ : (y : B) → f (g y) ＝ y
    ε′ y = sym (ε (f (g y))) ∙ ap f (η (g y)) ∙ ε y

    zig : (x : A) → ε′ (f x) ＝ ap f (η x)
    zig x =
      ε′ (f x)                                                    ＝⟨⟩
      sym (ε (f (g (f x))))  ∙ ap f ⌜ (η (g (f x))) ⌝ ∙ ε (f x)   ＝⟨ ap (λ e → sym (ε _) ∙ ap f e ∙ ε _) (homotopy-invert η) ⟩
      sym (ε (f (g (f x))))  ∙ ⌜ ap (f ∘ g ∘ f) (η x) ∙ ε (f x) ⌝ ＝˘⟨ ap¡ (homotopy-natural ε _) ⟩
      sym (ε (f (g (f x))))  ∙ ε (f (g (f x)))      ∙ ap f (η x)  ＝⟨ ∙-cancel-l (ε (f (g (f x)))) (ap f (η x)) ⟩
      ap f (η x)                                                  ∎

@0 fibre-paths : {f : A → B} {y : B}
               → {f1 f2 : fibre f y}
               → (f1 ＝ f2)
               ≃ (Σ[ γ ꞉ f1 .fst ＝ f2 .fst ] (ap f γ ∙ f2 .snd ＝ f1 .snd))
fibre-paths {f} {y} {f1} {f2} =
  Path (fibre f y) f1 f2                                                          ≃⟨ iso→equiv Σ-path-iso ₑ⁻¹ ⟩
  (Σ[ γ ꞉ f1 .fst ＝ f2 .fst ] (subst (λ x₁ → f x₁ ＝ _) γ (f1 .snd) ＝ f2 .snd)) ≃⟨ Σ-ap-snd (λ x → path→equiv (lemma x)) ⟩
  (Σ[ γ ꞉ f1 .fst ＝ f2 .fst ] (ap f γ ∙ f2 .snd ＝ f1 .snd))                     ≃∎
  where
    helper : (p′ : f (f1 .fst) ＝ y)
           →  (subst (λ x → f x ＝ y) refl (f1 .snd) ＝ p′)
           ＝ (ap f refl ∙ p′ ＝ f1 .snd)
    helper p′ =
      subst (λ x → f x ＝ y) refl (f1 .snd) ＝ p′ ＝⟨ ap₂ _＝_ (transport-refl _) refl ⟩
      (f1 .snd) ＝ p′                             ＝⟨ iso→path (sym , iso sym (λ x → refl) (λ x → refl)) ⟩
      ⌜ p′ ⌝ ＝ f1 .snd                           ＝˘⟨ ap¡ (∙-id-l _) ⟩
      refl ∙ p′ ＝ f1 .snd                        ＝⟨⟩
      ap f refl ∙ p′ ＝ f1 .snd                   ∎

    lemma : ∀ {x'} {p'} → (γ : f1 .fst ＝ x')
          →  (subst (λ x → f x ＝ _) γ (f1 .snd) ＝ p')
          ＝ (ap f γ ∙ p' ＝ f1 .snd)
    lemma {x'} {p'} p =
      J (λ x' γ → ∀ p' → (subst (λ x → f x ＝ _) γ (f1 .snd) ＝ p')
                       ＝ (ap f γ ∙ p' ＝ f1 .snd))
        helper p p'

@0 is-half-adjoint-equiv→is-equiv
  : {f : A → B}
  → is-half-adjoint-equiv f → is-equiv f
is-half-adjoint-equiv→is-equiv {A} {B} {f} (g , η , ε , zig) .equiv-proof y = fib , contract where
  fib : fibre f y
  fib = g y , ε y

  contract : (fib₂ : fibre f y) → fib ＝ fib₂
  contract (x , p) = (fibre-paths ₑ⁻¹) .fst (x≡gy , path) where
    x≡gy = ap g (sym p) ∙ η x

    path : ap f (ap g (sym p) ∙ η x) ∙ p ＝ ε y
    path =
      ap f (ap g (sym p) ∙ η x) ∙ p                   ＝⟨ ap₂ _∙_ (ap-comp-∙ f (ap g (sym p)) (η x)) refl ∙ sym (∙-assoc _ _ _) ⟩
      ap (λ x → f (g x)) (sym p) ∙ ⌜ ap f (η x) ⌝ ∙ p ＝⟨ ap! (zig _) ⟩ -- by the triangle identity
      ap (f ∘ g) (sym p) ∙ ⌜ ε (f x) ∙ p ⌝            ＝⟨ ap! (homotopy-natural ε p)  ⟩ -- by naturality of ε
      ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ∙ ε y         ＝⟨ ∙-assoc _ _ _ ⟩
      ⌜ ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ⌝ ∙ ε y     ＝˘⟨ ap¡ (ap-comp-∙ (f ∘ g) (sym p) p) ⟩
      ap (f ∘ g) ⌜ sym p ∙ p ⌝ ∙ ε y                  ＝⟨ ap! (∙-inv-r _) ⟩
      ap (f ∘ g) refl ∙ ε y                           ＝⟨⟩
      refl ∙ ε y                                      ＝⟨ ∙-id-l (ε y) ⟩
      ε y                                             ∎

@0 is-iso→is-equiv′
  : {f : A → B}
  → is-iso f → is-equiv f
is-iso→is-equiv′ = is-half-adjoint-equiv→is-equiv ∘ is-iso→is-half-adjoint-equiv

is-equiv→is-half-adjoint-equiv
  : {f : A → B}
  → is-equiv f → is-half-adjoint-equiv f
is-equiv→is-half-adjoint-equiv {f} eqv =
    is-equiv→inverse eqv
  , is-equiv→unit eqv
  , is-equiv→counit eqv
  , is-equiv→zig eqv
