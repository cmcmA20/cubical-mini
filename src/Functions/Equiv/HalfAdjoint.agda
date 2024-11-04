{-# OPTIONS --safe #-}
module Functions.Equiv.HalfAdjoint where

open import Foundations.Prelude

open import Functions.Fibration

private variable
  ℓ₁ ℓ₂ : Level
  A : Type ℓ₁
  B : Type ℓ₂
  f : A → B

is-half-adjoint-equiv : (f : A → B) → Type _
is-half-adjoint-equiv {A} {B} f =
  Σ[ g ꞉ (B → A) ]
  Σ[ η ꞉ g retraction-of′ f ]
  Σ[ ε ꞉ g section-of′ f ]
  Π[ x ꞉ A ] (ap f (η x) ＝ ε (f x))

qinv→is-half-adjoint-equiv : {f : A → B} → quasi-inverse f → is-half-adjoint-equiv f
qinv→is-half-adjoint-equiv {A} {B} {f} iiso =
  g , η #_ , ε′ , λ x → zig x ⁻¹
  where
    open quasi-inverse iiso renaming (inv to g ; inv-i to η ; inv-o to ε)
    ε′ : (y : B) → f (g y) ＝ y
    ε′ y = ε # (f (g y)) ⁻¹ ∙ ap f (η # g y) ∙ ε # y

    zig : (x : A) → ε′ (f x) ＝ ap f (η # x)
    zig x =
      ε′ (f x)                                                   ~⟨⟩
      ε # (f (g (f x))) ⁻¹ ∙ ap f (η # (g (f x))) ∙ ε # (f x)    ~⟨ _ ◁ ap (ap f) (homotopy-invert (η #_)) ▷ ε # f x ⟩
      ε # (f (g (f x))) ⁻¹ ∙ ap (f ∘ g ∘ f) (η # x) ∙ ε # (f x)  ~⟨ _ ◁ homotopy-natural (ε #_) (ap f (η # x)) ⟨
      ε # (f (g (f x))) ⁻¹ ∙ ε # (f (g (f x))) ∙ ap f (η # x)    ~⟨ ∙-cancel-l (ε # (f (g (f x)))) (ap f (η # x)) ⟩
      ap f (η # x)                                               ∎


@0 is-half-adjoint-equiv→is-equiv : is-half-adjoint-equiv f → is-equiv f
is-half-adjoint-equiv→is-equiv {f} (g , η , ε , zig) .equiv-proof y = fib , contract where
  fib : fibre f y
  fib = g y , ε y

  fibre-paths′ : {z@(a , p) z′@(a′ , p′) : fibre f y}
               → z ＝ z′
               ≃ Σ[ q ꞉ a ＝ a′ ] (ap f q ∙ p′ ＝ p)
  fibre-paths′ = fibre-paths ∙ Σ-ap-snd λ _ → flip-lₑ ∙ sym-≃

  contract : (fib₂ : fibre f y) → fib ＝ fib₂
  contract (x , p) = fibre-paths′ ⁻¹ $ x=gy , path where
    x=gy = ap g (p ⁻¹) ∙ η x

    path : ap f (ap g (p ⁻¹) ∙ η x) ∙ p ＝ ε y
    path =
      ap f (ap g (p ⁻¹) ∙ η x) ∙ p              ~⟨ ap-comp-∙ f _ (η x) ▷ p ⟩
      (ap (f ∘ g) (p ⁻¹) ∙ ap f (η x)) ∙ p      ~⟨ ∙-assoc _ _ p ⟨
      ap (f ∘ g) (p ⁻¹) ∙ ap f (η x) ∙ p        ~⟨ _ ◁ zig x ▷ p ⟩
      ap (f ∘ g) (p ⁻¹) ∙ (ε (f x) ∙ p)         ~⟨ _ ◁ homotopy-natural ε p ⟩
      ap (f ∘ g) (p ⁻¹) ∙ ap (f ∘ g) p ∙ ε y    ~⟨ ∙-assoc _ _ (ε y) ⟩
      (ap (f ∘ g) (p ⁻¹) ∙ ap (f ∘ g) p) ∙ ε y  ~⟨ ap-comp-∙ (f ∘ g) (p ⁻¹) p ▷ ε y ⟨
      ap (f ∘ g) (p ⁻¹ ∙ p) ∙ ε y               ~⟨ ap (ap (f ∘ g)) (∙-inv-i (p ⁻¹)) ▷ ε y ⟩
      ap (f ∘ g) refl ∙ ε y                     ~⟨⟩
      refl ∙ ε y                                ~⟨ ∙-id-o (ε y) ⟩
      ε y                                       ∎

@0 qinv→is-equiv′ : {f : A → B} → quasi-inverse f → is-equiv f
qinv→is-equiv′ = is-half-adjoint-equiv→is-equiv ∘ qinv→is-half-adjoint-equiv

is-equiv→is-half-adjoint-equiv : is-equiv f → is-half-adjoint-equiv f
is-equiv→is-half-adjoint-equiv {f} eqv =
    is-equiv→inverse eqv
  , is-equiv→unit eqv
  , is-equiv→counit eqv
  , is-equiv→zig eqv
