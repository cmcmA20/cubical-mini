{-# OPTIONS --safe #-}
module Categories.Displayed.Base where

open import Meta.Prelude
  hiding (_∘_; id)

open import Meta.Projection
open import Meta.Reflection.Base

open import Structures.n-Type

open import Categories.Base

open import Data.Bool.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Term

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

  _＝[]⟨_⟨_ : ∀ {a b x y} {f g h : Hom a b} {p : g ＝ f} {q : g ＝ h}
             → (f′ : Hom[ f ] x y) {g′ : Hom[ g ] x y} {h′ : Hom[ h ] x y}
             → g′ ＝[ p ] f′ → g′ ＝[ q ] h′ → f′ ＝[ sym p ∙ q ] h′
  f′ ＝[]⟨ p′ ⟨ q′ = symᴾ p′ ∙[] q′

  syntax ∙[-]-syntax p p′ q′ = p′ ∙[ p ] q′
  syntax ＝[]⟨⟩-syntax f′ q′ p′ = f′ ＝[]⟨ p′ ⟩ q′
  syntax ＝[-]⟨⟩-syntax p f′ q′ p′ = f′ ＝[ p ]⟨ p′ ⟩ q′

  infixr 30 _∙[]_ ∙[-]-syntax
  infixr 2 ＝[]⟨⟩-syntax ＝[-]⟨⟩-syntax _＝[]⟨_⟨_

  hom[-]-set′ : ∀ {x y} {f : Hom x y} {x′ y′} → is-set (Hom[ f ] x′ y′)
  hom[-]-set′ = Hom[ _ ]-set _ _

  instance
    H-Level-Hom[-] : ∀ {n} {a b} {f : Hom a b} {a′ b′} → H-Level (2 + n) (Hom[ f ] a′ b′)
    H-Level-Hom[-] = hlevel-basic-instance 2 hom[-]-set′

    Refl-Hom[-] : ∀ {a} → Refl Hom[ id {a} ]
    Refl-Hom[-] .refl = idᵈ

    Trans-Hom[-] : ∀ {a b c} {f : Hom a b} {g : Hom b c} → Trans Hom[ f ] Hom[ g ] Hom[ f ∙ g ]
    Trans-Hom[-] ._∙_ f′ g′ = g′ ∘ᵈ f′

instance
  open Struct-proj-desc

  hlevel-proj-displayed : Struct-proj-desc true (quote Displayed.Hom[_])
  hlevel-proj-displayed .has-level = quote Displayed.hom[-]-set′
  hlevel-proj-displayed .upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-displayed .get-level _ = pure (lit (nat 2))
  hlevel-proj-displayed .get-argument (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ x v∷ _) = pure x
  hlevel-proj-displayed .get-argument _ = type-error []
