{-# OPTIONS --safe #-}
module Categories.Displayed.Base where

open import Foundations.Base
  hiding (id; _∘_)
open import Foundations.HLevel
open import Foundations.Path
open import Categories.Base

record Displayed {o ℓ} (B : Precategory o ℓ)
                 (o′ ℓ′ : Level) : Type (o ⊔ ℓ ⊔ ℓsuc o′ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  open Precategory B

  field
    Ob[_] : Ob → Type o′
    Hom[_] : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓ′
    Hom[_]-set : ∀ {a b} (f : Hom a b) (x : Ob[ a ]) (y : Ob[ b ])
               → is-set (Hom[ f ] x y)
    idᵈ  : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x
    _∘ᵈ_ : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b}
         → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

  infixr 40 _∘ᵈ_

  _＝[_]_ : ∀ {a b x y} {f g : Hom a b} → Hom[ f ] x y → f ＝ g → Hom[ g ] x y → Type ℓ′
  _＝[_]_ {a} {b} {x} {y} f′ p g′ = ＜ f′ ／ (λ i → Hom[ p i ] x y) ＼ g′ ＞

  infix 30 _＝[_]_

  field
    id-rᵈ : ∀ {a b x y} {f : Hom a b} (f′ : Hom[ f ] x y) → (f′ ∘ᵈ idᵈ) ＝[ id-r f ] f′
    id-lᵈ : ∀ {a b x y} {f : Hom a b} (f′ : Hom[ f ] x y) → (idᵈ ∘ᵈ f′) ＝[ id-l f ] f′
    assocᵈ : ∀ {a b c d w x y z} {f : Hom c d} {g : Hom b c} {h : Hom a b}
           → (f′ : Hom[ f ] y z) (g′ : Hom[ g ] x y) (h′ : Hom[ h ] w x)
           → f′ ∘ᵈ (g′ ∘ᵈ h′) ＝[ assoc f g h ] ((f′ ∘ᵈ g′) ∘ᵈ h′)

  _∙[]_ : ∀ {a b x y} {f g h : Hom a b} {p : f ＝ g} {q : g ＝ h}
        → {f′ : Hom[ f ] x y} {g′ : Hom[ g ] x y} {h′ : Hom[ h ] x y}
        → f′ ＝[ p ] g′ → g′ ＝[ q ] h′ → f′ ＝[ p ∙ q ] h′
  _∙[]_ {x} {y} p′ q′ = _∙ᴾ_ {B = λ f → Hom[ f ] x y} p′ q′

  ∙[-]-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ＝ g) {q : g ＝ h}
              → {f′ : Hom[ f ] x y} {g′ : Hom[ g ] x y} {h′ : Hom[ h ] x y}
              → f′ ＝[ p ] g′ → g′ ＝[ q ] h′ → f′ ＝[ p ∙ q ] h′
  ∙[-]-syntax {x} {y} p p′ q′ = _∙ᴾ_ {B = λ f → Hom[ f ] x y} p′ q′

  ＝[]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} {p : f ＝ g} {q : g ＝ h}
                → (f′ : Hom[ f ] x y) {g′ : Hom[ g ] x y} {h′ : Hom[ h ] x y}
                → g′ ＝[ q ] h′ → f′ ＝[ p ] g′ → f′ ＝[ p ∙ q ] h′
  ＝[]⟨⟩-syntax _ q′ p′ = p′ ∙[] q′

  ＝[-]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ＝ g) {q : g ＝ h}
                 → (f′ : Hom[ f ] x y) {g′ : Hom[ g ] x y} {h′ : Hom[ h ] x y}
                 → g′ ＝[ q ] h′ → f′ ＝[ p ] g′ → f′ ＝[ p ∙ q ] h′
  ＝[-]⟨⟩-syntax f′ p q′ p′ = p′ ∙[] q′

  _＝[]˘⟨_⟩_ : ∀ {a b x y} {f g h : Hom a b} {p : g ＝ f} {q : g ＝ h}
             → (f′ : Hom[ f ] x y) {g′ : Hom[ g ] x y} {h′ : Hom[ h ] x y}
             → g′ ＝[ p ] f′ → g′ ＝[ q ] h′ → f′ ＝[ sym p ∙ q ] h′
  f′ ＝[]˘⟨ p′ ⟩ q′ = symP p′ ∙[] q′

  syntax ∙[-]-syntax p p′ q′ = p′ ∙[ p ] q′
  syntax ＝[]⟨⟩-syntax f′ q′ p′ = f′ ＝[]⟨ p′ ⟩ q′
  syntax ＝[-]⟨⟩-syntax p f′ q′ p′ = f′ ＝[ p ]⟨ p′ ⟩ q′

  infixr 30 _∙[]_ ∙[-]-syntax
  infixr 2 ＝[]⟨⟩-syntax ＝[-]⟨⟩-syntax _＝[]˘⟨_⟩_

  instance
    H-Level-Hom[-] : ∀ {n} {a b} {f : Hom a b} {a′ b′} → H-Level (2 + n) (Hom[ f ] a′ b′)
    H-Level-Hom[-] = hlevel-basic-instance 2 (Hom[ _ ]-set _ _)
