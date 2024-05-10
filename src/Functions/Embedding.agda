{-# OPTIONS --safe #-}
module Functions.Embedding where

open import Meta.Prelude
open import Meta.Extensionality

open import Structures.n-Type

open import Data.Unit.Base

open import Functions.Fibration

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  C : Type ℓ″
  g : B → C

Injective : (A → B) → Type _
Injective f = ∀ {x y} → f x ＝ f y → x ＝ y

_↣_ : Type ℓ → Type ℓ′ → Type _
A ↣ B = Σ[ f ꞉ (A → B) ] Injective f

is-embedding : (A → B) → Type _
is-embedding f = ∀ y → is-prop (fibre f y)

_↪_ : Type ℓ → Type ℓ′ → Type _
A ↪ B = Σ[ f ꞉ (A → B) ] is-embedding f

instance
  Funlike-Inj : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (A ↣ B) A (λ _ → B)
  Funlike-Inj ._#_ = fst

  Funlike-Emb : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (A ↪ B) A (λ _ → B)
  Funlike-Emb ._#_ = fst

set-injective→is-embedding
  : {f : A → B} → is-set B → Injective f
  → is-embedding f
set-injective→is-embedding B-set inj x (f*x , p) (f*x′ , q) =
  Σ-prop-path! (inj (p ∙ q ⁻¹)) where instance _ = hlevel-basic-instance 2 B-set

is-embedding→injective
  : is-embedding f → Injective f
is-embedding→injective prop p = ap fst (prop _ (_ , p) (_ , refl))

↪→↣ : A ↪ B → A ↣ B
↪→↣ = second is-embedding→injective

set-injective≃is-embedding
  : {f : A → B} → is-set A → is-set B
  → Injective f ≃ is-embedding f
set-injective≃is-embedding A-set B-set =
  prop-extₑ! (set-injective→is-embedding B-set)
             (is-embedding→injective)
  where instance _ = hlevel-basic-instance 2 A-set

@0 subtype-classifier
  : {B : Type ℓ}
  → Σ[ A ꞉ Type ℓ ] A ↪ B
  ≃ (B → Σ[ T ꞉ Type ℓ ] is-prop T)
subtype-classifier {ℓ} = map-classifier {ℓ = ℓ} is-prop

module @0 subtype-classifier {ℓ} {B : Type ℓ} = Equiv (subtype-classifier {B = B})


subset-proj-is-embedding
  : {B : A → Type ℓ′}
  → (∀ x → is-prop (B x))
  → is-embedding {A = Σ _ B} fst
subset-proj-is-embedding {B} B-prop x = ≃→is-of-hlevel 1 (Σ-fibre-equiv B x) (B-prop _)

is-embedding→monic
  : is-embedding f
  → ∀ {C : Type ℓ″} (g h : C → A) → f ∘ g ＝ f ∘ h → g ＝ h
is-embedding→monic {f} emb g h p =
  fun-ext λ x → ap fst (emb _ (g x , refl) (h x , p ⁻¹ $ₚ x))

set-monic→is-embedding
  : {A : Type ℓ} {B : Type ℓ′} {f : A → B} → is-set B
  → (∀ {C : Set ℓ″} (g h : C →̇ A) → f ∘ g ＝ f ∘ h → g ＝ h)
  → is-embedding f
set-monic→is-embedding {f} B-set monic =
  set-injective→is-embedding B-set λ {x} {y} p →
    monic {C = el! $ Lift _ ⊤} (λ _ → x) (λ _ → y) (fun-ext (λ _ → p)) $ₚ _


preimage-is-prop→is-embedding : (∀ x → is-prop (fibre f (f x))) → is-embedding f
preimage-is-prop→is-embedding {f} pffx y a = subst (λ φ → is-prop (fibre f φ))
  (a .snd) (pffx (a .fst)) a

preimage-is-contr→is-embedding : (∀ x → is-contr (fibre f (f x))) → is-embedding f
preimage-is-contr→is-embedding cffx =
 preimage-is-prop→is-embedding (is-contr→is-prop ∘ cffx)


-- TODO isn't `ap f` unique?
Cancellable : (A → B) → Type _
Cancellable f = ∀ {x y} → (f x ＝ f y) ≃ (x ＝ y)

is-equiv-on-paths : (A → B) → Type _
is-equiv-on-paths f = ∀ {x y} → is-equiv {B = f x ＝ f y} (ap f)

is-equiv-on-paths→cancellable : is-equiv-on-paths f → Cancellable f
is-equiv-on-paths→cancellable f-eop = _ , is-equiv-inv f-eop

@0 is-equiv-on-paths→is-embedding : is-equiv-on-paths f → is-embedding f
is-equiv-on-paths→is-embedding ep b fib₁ fib₂ =
  fibre-equality≃fibre-on-paths ⁻¹ $ (ep .equiv-proof (fib₁ .snd ∙ sym (fib₂ .snd)) .fst)

cancellable→is-embedding : Cancellable f → is-embedding f
cancellable→is-embedding can = preimage-is-contr→is-embedding λ x → ≃→is-of-hlevel 0 (Σ-ap-snd (λ _ → can)) $
  (x , refl) , λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

is-embedding→is-equiv-on-paths : is-embedding f → is-equiv-on-paths f
is-embedding→is-equiv-on-paths {f} emb = total-is-equiv→fibrewise-is-equiv {f = λ y p → ap {y = y} f p}
  (is-contr→is-equiv
    ((_ , refl) , λ (y , p) i → p i , λ j → p (i ∧ j))
    ((_ , refl) , ≃→is-of-hlevel 1 (Σ-ap-snd (λ _ → sym-≃)) (emb _) _))

@0 is-embedding≃is-equiv-on-paths : is-embedding f ≃ is-equiv-on-paths f
is-embedding≃is-equiv-on-paths = prop-extₑ! is-embedding→is-equiv-on-paths is-equiv-on-paths→is-embedding

is-embedding→is-of-hlevel
  : ∀ n → {f : A → B} → is-embedding f
  → is-of-hlevel (suc n) B
  → is-of-hlevel (suc n) A
is-embedding→is-of-hlevel n {f} emb a-hl = ≃→is-of-hlevel (suc n) (total-equiv f) $
  Σ-is-of-hlevel (suc n) a-hl λ x → is-prop→is-of-hlevel-suc {h = n} (emb x)

↪→is-of-hlevel
  : ∀ n → ⦃ le : 1 ≤ʰ n ⦄
  → B ↪ A
  → is-of-hlevel n A
  → is-of-hlevel n B
↪→is-of-hlevel (suc n) ⦃ s≤ʰs le ⦄ f = is-embedding→is-of-hlevel n (f .snd)

is-equiv→is-embedding : is-equiv f → is-embedding f
is-equiv→is-embedding r y = is-contr→is-prop $ r .equiv-proof y

≃→↪ : A ≃ B → A ↪ B
≃→↪ = second is-equiv→is-embedding

is-iso→is-embedding : is-iso f → is-embedding f
is-iso→is-embedding = is-equiv→is-embedding ∘ is-iso→is-equiv

≅→↪ : A ≅ B → A ↪ B
≅→↪ = second is-iso→is-embedding

instance
  Refl-Inj : Refl (_↣_ {ℓ})
  Refl-Inj .refl = id , id

  Refl-Emb : Refl (_↪_ {ℓ})
  Refl-Emb .refl = id , is-equiv→is-embedding id-is-equiv

  Trans-Inj : Trans (_↣_ {ℓ} {ℓ′}) (_↣_ {ℓ′ = ℓ″}) _↣_
  Trans-Inj ._∙_ (f , f-inj) (g , g-inj) = g ∘ f , f-inj ∘ g-inj

  Trans-Emb : Trans (_↪_ {ℓ} {ℓ′}) (_↪_ {ℓ′ = ℓ″}) _↪_
  Trans-Emb ._∙_ (f , f-emb) (g , g-emb) = g ∘ f , λ c →
    ≃→is-of-hlevel 1 fibre-comp (Σ-is-of-hlevel 1 (g-emb c) (f-emb ∘ fst))

is-embedding-comp+is-embedding-outer→is-embedding-inner
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {f : A → B} {g : B → C}
  → is-embedding (g ∘ f) → is-embedding g → is-embedding f
is-embedding-comp+is-embedding-outer→is-embedding-inner {f} {g} gfe ge =
  cancellable→is-embedding $ (ap g , is-embedding→is-equiv-on-paths ge) ∙
    (ap (g ∘ f) , is-embedding→is-equiv-on-paths gfe) ⁻¹

opaque
  pullback-identity-system
    : {A : Type ℓ} {B : Type ℓ′} {R : B → B → Type ℓ″} {r : ∀ b → R b b}
      (ids : is-identity-system R r)
      (f : A ↪ B)
    → is-identity-system (λ (x y : A) → R (f $ x) (f $ y)) (λ _ → r _)
  pullback-identity-system     ids (f , f-emb) .to-path {a} {b} x = ap fst $
    f-emb (f b) (a , ids .to-path x) (b , refl)
  pullback-identity-system {R} ids (f , f-emb) .to-path-over {a} {b} p i =
    comp
      (λ j → R (f a) (f-emb (f b) (a , ids .to-path p) (b , refl) i .snd (~ j)))
      (∂ i) λ where
        k (i = i0) → ids .to-path-over p (~ k ∨ i)
        k (i = i1) → p
        k (k = i0) → ids .to-path-over p (~ k)

↪→extensional
  : A ↪ B
  → Extensional B ℓ″
  → Extensional A ℓ″
↪→extensional f ext .Pathᵉ x y = Pathᵉ ext (f $ x) (f $ y)
↪→extensional f ext .reflᵉ x = reflᵉ ext (f $ x)
↪→extensional f ext .idsᵉ = pullback-identity-system (ext .idsᵉ) f

Σ-prop→extensional
  : {A : Type ℓ} {B : A → Type ℓ′}
  → (∀ x → is-prop (B x))
  → Extensional A ℓ″
  → Extensional (Σ A B) ℓ″
Σ-prop→extensional B-prop = ↪→extensional (fst , subset-proj-is-embedding B-prop)


-- Automation

↪→is-of-hlevel!
  : ∀ n → B ↪ A
  → ⦃ le : 1 ≤ʰ n ⦄
  → ⦃ hl : H-Level n A ⦄
  → is-of-hlevel n B
↪→is-of-hlevel! n f = ↪→is-of-hlevel n f hlevel!

set-injective→is-embedding!
  : {f : A → B} → ⦃ B-set : H-Level 2 B ⦄ → Injective f
  → is-embedding f
set-injective→is-embedding! = set-injective→is-embedding hlevel!

set-injective→extensional!
  : ⦃ B-set : H-Level 2 B ⦄
  → {f : A → B}
  → Injective f
  → Extensional B ℓ″
  → Extensional A ℓ″
set-injective→extensional! {f} inj ext =
  ↪→extensional (f , set-injective→is-embedding! inj) ext

Σ-prop→extensional!
  : {A : Type ℓ} {B : A → Type ℓ′}
  → ⦃ B-pr : ∀ {x} → H-Level 1 (B x) ⦄
  → Extensional A ℓ″
  → Extensional (Σ A B) ℓ″
Σ-prop→extensional! = Σ-prop→extensional hlevel!

instance
  Extensional-↪
    : {A : Type ℓ} ⦃ sb : Extensional (A → B) ℓ″ ⦄
    → Extensional (A ↪ B) ℓ″
  Extensional-↪ ⦃ sb ⦄ = Σ-prop→extensional! sb
