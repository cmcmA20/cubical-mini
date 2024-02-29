{-# OPTIONS --safe #-}
module Structures.Base where

open import Foundations.Base
  hiding (_∙_; Σ-syntax; Π-syntax; ∀-syntax)
open import Foundations.HLevel.Base
open import Foundations.Pi
  hiding (Π-syntax; ∀-syntax)
open import Foundations.Sigma
  hiding (Σ-syntax)
open import Foundations.Univalence public

open import Meta.Groupoid
open import Meta.Underlying

open import Data.Unit.Properties

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

constant-str : (A : Type ℓ) → Structure {ℓ₁} ℓ (λ _ → A)
constant-str T .is-hom (A , x) (B , y) f = x ＝ y

constant-str-is-univalent : is-univalent (constant-str {ℓ₁ = ℓ₁} A)
constant-str-is-univalent _ = refl!

constant-action : (A : Type ℓ) → Equiv-action {ℓ = ℓ₁} (λ X → A)
constant-action _ _ = refl!

constant-action-is-transport
  : is-transport-str {ℓ = ℓ₁} (constant-action A)
constant-action-is-transport _ _ = transport-refl _ ⁻¹


pointed-str : Structure ℓ id
pointed-str .is-hom (_ , x) (_ , y) f = f # x ＝ y

@0 pointed-str-is-univalent : is-univalent (pointed-str {ℓ})
pointed-str-is-univalent f = ua-pathP≃path _

opaque
  unfolding ua
  id-action-is-transport : is-transport-str {ℓ} {ℓ} id
  id-action-is-transport _ _ = transport-refl _ ⁻¹

Type∙ : ∀ ℓ → Type (ℓsuc ℓ)
Type∙ _ = Type-with pointed-str


product-str : Structure ℓ S → Structure ℓ₂ T → Structure _ (λ X → S X × T X)
product-str S T .is-hom (A , x , y) (B , x′ , y′) f =
  S .is-hom (A , x) (B , x′) f × T .is-hom (A , y) (B , y′) f

@0 product-str-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                            → is-univalent σ → is-univalent τ
                            → is-univalent (product-str σ τ)
product-str-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ {X , x , y} {Y , x′ , y′} f =
  σ .is-hom (X , x) (Y , x′) f × τ .is-hom (X , y) (Y , y′) f               ≃⟨ ×-ap (θ₁ f) (θ₂ f) ⟩
  ＜ x ／ (λ i → S (ua f i)) ＼ x′ ＞ × ＜ y ／ (λ i → T (ua f i)) ＼ y′ ＞  ≃⟨ iso→equiv Σ-pathP-iso ⟩
  ＜ x , y ／ (λ i → S (ua f i) × T (ua f i)) ＼ x′ , y′ ＞                  ≃∎

product-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X × T X)
product-action actx acty eqv = ×-ap (actx eqv) (acty eqv)

@0 product-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (product-action α β)
product-action-is-transport α-tr β-tr e s =
 Σ-pathP (α-tr e (s .fst)) (β-tr e (s .snd))


-- naive one, do not use
private
  function-str′ : Structure ℓ₁ S → Structure ℓ₂ T → Structure _ (λ X → S X → T X)
  function-str′ {S} σ τ .is-hom (A , f) (B , g) h =
    {s : S A} {t : S B} → σ .is-hom (A , s) (B , t) h
                        → τ .is-hom (A , f s) (B , g t) h

  @0 function-str′-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                                → is-univalent σ → is-univalent τ
                                → is-univalent (function-str′ σ τ)
  function-str′-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ eqv =
    Π-impl-cod-≃ (λ s → Π-impl-cod-≃ λ t → function-≃ (θ₁ eqv) (θ₂ eqv)) ∙ fun-ext-dep-≃


function-str : Equiv-action S → Structure ℓ T → Structure _ (λ X → S X → T X)
function-str {S} act str .is-hom (A , f) (B , g) e =
  Π[ s ꞉ S A ] str .is-hom (A , f s) (B , g (act e .fst s)) e

@0 function-str-is-univalent
  : (α : Equiv-action S) → is-transport-str α
  → (τ : Structure ℓ T) → is-univalent τ
  → is-univalent (function-str α τ)
function-str-is-univalent {S} {T} α α-tr τ τ-univ {X , f} {Y , g} eqv =
  Π[ s ꞉ S X ] τ .is-hom (X , f s) (Y , _) eqv         ≃⟨ Π-cod-≃ (λ s → τ-univ eqv ∙ path→equiv (ap (PathP (λ i → T (ua eqv i)) (f s) ∘ g) (α-tr _ _))) ⟩
  Π[ s ꞉ S X ] ＜ f s ／ (λ i → T (ua eqv i)) ＼ _ ＞  ≃⟨ hetero-homotopy≃homotopy ⁻¹ ∙ fun-ext-dep-≃ ⟩
  _                                                    ≃∎

function-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X → T X)
function-action actx acty eqv = function-≃ (actx eqv) (acty eqv)

@0 function-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (function-action α β)
function-action-is-transport {S} {α} {β} α-tr β-tr eqv f =
  fun-ext λ x → ap (β eqv .fst ∘ f) (sym-transport-str α α-tr eqv x)
              ∙ β-tr eqv (f (subst S (ua eqv ⁻¹) x))


property : (S : Type ℓ → Type ℓ₁) → (∀ A → is-prop (S A)) → Structure 0ℓ S
property _ _ .is-hom _ _ _ = ⊤

@0 property-is-univalent : {S-prop : _} → is-univalent {S = S} (property S S-prop)
property-is-univalent {S-prop} {X = _ , s} {Y = _ , t} _ =
  is-contr→equiv-⊤ (
    inhabited-prop-is-contr (is-prop→pathP (λ _ → S-prop _) s t)
                            (pathP-is-of-hlevel 1 (S-prop _))
  ) ⁻¹

@0 transfer-property
  : {S-prop : _}
  → (A : Type-with (property S S-prop)) (B : Type ℓ)
  → A .fst ≃ B
  → S B
transfer-property {S} A B eqv = subst S (ua eqv) (A .snd)

-- TODO use `property`?
module _
  (σ : Structure ℓ S)
  (axioms : (X : _) → S X → Type ℓ₃)
  where

  axiom-str : Structure ℓ (λ X → Σ[ s ꞉ S X ] (axioms X s))
  axiom-str .is-hom (A , s , a) (B , t , b) f =
    σ .is-hom (A , s) (B , t) f

  module _
    (univ : is-univalent σ)
    (axioms-prop : ∀ {X} {s} → is-prop (axioms X s)) where opaque
    unfolding is-of-hlevel

    @0 axiom-str-univalent : is-univalent axiom-str
    axiom-str-univalent {X = A , s , a} {Y = B , t , b} f =
      σ .is-hom (A , s) (B , t) f
        ≃⟨ univ f ⟩
      ＜ s ／ (λ i → S (ua f i)) ＼ t ＞
        ≃˘⟨ Σ-contract-snd (λ x → pathP-is-of-hlevel 0 (b , (axioms-prop b))) ⟩
      Σ[ p ꞉ ＜ s ／ (λ i → S (ua f i)) ＼ t ＞ ] ＜ a ／ (λ i → axioms (ua f i) (p i)) ＼ b ＞
        ≃⟨ iso→equiv Σ-pathP-iso ⟩
      _
        ≃∎

@0 transfer-axioms
  : {σ : Structure ℓ S} {univ : is-univalent σ}
    {axioms : (X : _) → S X → Type ℓ₃}
  → (A : Type-with (axiom-str σ axioms)) (B : Type-with σ)
  → (A .fst , A .snd .fst) ≃[ σ ] B
  → axioms (B .fst) (B .snd)
transfer-axioms {univ} {axioms} A B eqv =
  subst (axioms $²_) (sip univ eqv) (A .snd .snd)
