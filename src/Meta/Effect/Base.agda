{-# OPTIONS --safe #-}
module Meta.Effect.Base where

open import Foundations.Base

open import Meta.Brackets

open import Data.Container.Base
  public
  renaming ( Container to Signature
           )
open import Data.Container.Instances.Brackets
open Signature
  public
  renaming ( Shape    to Op
           ; Position to Arity
           )
open import Data.Sum.Base

private variable
  s p : Level
  Δ Δ′ Δ₀ Δ₁ : Signature s p

infixr 12 _⊕_
_⊕_ : Signature s p → Signature s p → Signature s p
(S₁ ▶ P₁) ⊕ (S₂ ▶ P₂) = S₁ ⊎ S₂ ▶ [ P₁ , P₂ ]ᵤ

data _∼_▸_ {s p} : Signature s p → Signature s p → Signature s p → Type (ℓsuc (s ⊔ p)) where
  ins  :                 (Δ₀ ⊕ Δ′) ∼ Δ₀ ▸ Δ′
  sift : (Δ ∼ Δ₀ ▸ Δ′) → (Δ₁ ⊕ Δ ) ∼ Δ₀ ▸ (Δ₁ ⊕ Δ′)

instance
  insert▸ : (Δ₀ ⊕ Δ′) ∼ Δ₀ ▸ Δ′
  insert▸ = ins

  sift▸ : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ → ((Δ₁ ⊕ Δ) ∼ Δ₀ ▸ (Δ₁ ⊕ Δ′))
  sift▸ ⦃ w ⦄ = sift w
  {-# OVERLAPPABLE sift▸ #-}

inj▸ₗ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Op Δ₀  → Op Δ
inj▸ₗ ⦃ (ins) ⦄  = inl
inj▸ₗ ⦃ sift p ⦄ = inr ∘ inj▸ₗ ⦃ p ⦄

inj▸ᵣ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Op Δ′  → Op Δ
inj▸ᵣ ⦃ (ins) ⦄  = inr
inj▸ᵣ ⦃ sift p ⦄ = [ inl , inr ∘ inj▸ᵣ ⦃ p ⦄ ]ᵤ

proj-ret▸ₗ : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ {op : Op Δ₀} → Arity Δ (inj▸ₗ op) → Arity Δ₀ op
proj-ret▸ₗ ⦃ (ins) ⦄ = id
proj-ret▸ₗ ⦃ sift w ⦄ = proj-ret▸ₗ ⦃ w ⦄

proj-ret▸ᵣ : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ {op : Op Δ′} → Arity Δ (inj▸ᵣ op) → Arity Δ′ op
proj-ret▸ᵣ ⦃ (ins) ⦄ = id
proj-ret▸ᵣ ⦃ sift w ⦄ {op = inl x} = id
proj-ret▸ᵣ ⦃ sift w ⦄ {op = inr y} = proj-ret▸ᵣ ⦃ w ⦄

inj▸ₗ-ret≡ : ⦃ p : Δ ∼ Δ₀ ▸ Δ′ ⦄ (op : Op Δ₀)
           → Arity Δ (inj▸ₗ op) ＝ Arity Δ₀ op
inj▸ₗ-ret≡ ⦃ (ins) ⦄ _  = refl
inj▸ₗ-ret≡ ⦃ sift p ⦄    = inj▸ₗ-ret≡ ⦃ p ⦄

inj▸ᵣ-ret≡ : ⦃ p : Δ ∼ Δ₀ ▸ Δ′ ⦄ (op : Op Δ′)
           → Arity Δ (inj▸ᵣ op) ＝ Arity Δ′ op
inj▸ᵣ-ret≡ ⦃ (ins) ⦄ op  = refl
inj▸ᵣ-ret≡ ⦃ sift p ⦄ (inl x) = refl
inj▸ᵣ-ret≡ ⦃ sift p ⦄ (inr x) = inj▸ᵣ-ret≡ ⦃ p ⦄ x

case▸ : ∀{ℓ}{B : Type ℓ}
      → ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄
      → Op Δ
      → (Op Δ₀  → B)
      → (Op Δ′  → B)
      → B
case▸ ⦃ (ins) ⦄ x f g = [ f , g ]ᵤ x
case▸ ⦃ sift p ⦄ x f g = [ g ∘ inl , (λ y → case▸ ⦃ p ⦄ y f (g ∘ inr)) ]ᵤ x

case▸≡ : ∀{ℓ} {B : Type ℓ}
         ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄
       → (op : Op Δ)
       → ((op′ : Op Δ₀) → op ＝ inj▸ₗ op′ → B)
       → ((op′ : Op Δ′) → op ＝ inj▸ᵣ op′ → B)
       → B
case▸≡ ⦃ (ins) ⦄ (inl x) f g = f x refl
case▸≡ ⦃ (ins) ⦄ (inr y) f g = g y refl
case▸≡ ⦃ w = sift p ⦄ (inl x) f g = g (inl x) refl
case▸≡ ⦃ w = sift p ⦄ (inr y) f g = case▸≡ ⦃ p ⦄ y (λ op′ → f op′ ∘ ap inr) (λ op′ → g (inr op′) ∘ ap inr)


record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀     : ∀ {ℓ} → Type ℓ → Type (adj ℓ)

record _-Alg[_] {ℓ s p} (𝔽 : Signature s p) (A : Type ℓ) : Type (ℓ ⊔ s ⊔ p) where
  no-eta-equality
  constructor mk-alg
  field unalg : ⟦ 𝔽 ⟧ A → A

open _-Alg[_]

EAlg : ∀ {o a} (𝔽 : Signature o a) (M : Effect) → Typeω
EAlg 𝔽 M = ∀ {ℓ} {A : Type ℓ} → 𝔽 -Alg[ M.₀ A ]
  where module M = Effect M

data Syntax {v o a} (𝔽 : Signature o a) (V : Type v) : Type (v ⊔ o ⊔ a) where
  var    : V → Syntax 𝔽 V
  impure : ⟦ 𝔽 ⟧ (Syntax 𝔽 V) → Syntax 𝔽 V

instance
  ⟦⟧-Syntax
    : ∀{o a c v} {𝔽 : Signature o a} {C : Type c} {V : Type v}
    → ⟦⟧-notation (Syntax 𝔽 V)
  ⟦⟧-Syntax {𝔽} {C} {V} = brackets (𝔽 -Alg[ C ] → (V → C) → C) go
    where
    go : Syntax 𝔽 V → 𝔽 -Alg[ C ] → (V → C) → C
    go (var x)          φ ρ = ρ x
    go (impure (o , k)) φ ρ = φ .unalg (o , λ i → go (k i) φ ρ)

  EAlg-Syntax
    : ∀{o a} {𝔽 : Signature o a}
    → EAlg 𝔽 (eff (Syntax 𝔽))
  EAlg-Syntax .unalg = impure

to-front : ∀{ℓ}{A : Type ℓ} ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ → Syntax Δ A → Syntax (Δ₀ ⊕ Δ′) A
to-front {Δ₀ = Δ₀} ⦃ w ⦄ (var x) = var x
to-front {Δ₀ = Δ₀} ⦃ (ins) ⦄ (impure (op , k)) = impure (op , to-front ⦃ ins ⦄ ∘ k)
to-front {Δ₀ = Δ₀} ⦃ sift w ⦄ (impure (inl op , k)) = impure ((inr (inl op)) , to-front ⦃ sift w ⦄ ∘ k)
to-front {Δ₀ = Δ₀} ⦃ sift {Δ} {Δ′} w ⦄ t@(impure (inr op , k)) = case▸≡ ⦃ w ⦄ op
  (λ op′ eq →
    impure
      ((inl op′)
      ,
      ( to-front ⦃ sift w ⦄
      ∘ k
      ∘ transport (sym (inj▸ₗ-ret≡ ⦃ w ⦄ op′) ∙ ap (Arity Δ) (sym eq)))))
  (λ op′ eq →
    impure ((inr (inr op′))
      ,
      ( to-front ⦃ sift w ⦄
      ∘ k
      ∘ transport (sym (inj▸ᵣ-ret≡ ⦃ w ⦄ op′) ∙ ap (Arity Δ) (sym eq)))))

run
  : ∀{ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄
  → {M : Effect} (let module M = Effect M)
  → EAlg Δ M → Syntax Δ A → (M.₀ A → Syntax Δ′ B)
run {A} al x m =
  let qwe = al {A = A} .unalg
  in ⟦ x ⟧ (mk-alg λ (o , k) → impure ({!!} , {!!})) {!!}
