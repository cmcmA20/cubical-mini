{-# OPTIONS --safe #-}
module Data.Reflection.Properties where

open import Foundations.Prelude

open import Data.Id.Inductive
open import Data.Reflection.Abs
open import Data.Reflection.Argument
open import Data.Reflection.Meta
open import Data.Reflection.Name

-- wtf agda?
private module M where primitive
  primMetaToNatInjective : ∀ x y → meta→ℕ x ＝ⁱ meta→ℕ y → x ＝ⁱ y

open M
  public
  renaming ( primMetaToNatInjective to meta→ℕ-injⁱ )

meta→ℕ-inj : {a b : Meta} → meta→ℕ a ＝ meta→ℕ b → a ＝ b
meta→ℕ-inj = Id≃path.to ∘ meta→ℕ-injⁱ _ _ ∘ Id≃path.from

private variable
  ℓ : Level
  A : Type ℓ

abs-ext
  : {x y : Abs A}
  → abs-name x ＝ abs-name y
  → abs-binder x ＝ abs-binder y
  → x ＝ y
abs-ext {x = abs s x} {abs t y} p q = ap² abs p q

modality-ext
  : {x y : Modality}
  → modality→relevance x ＝ modality→relevance y
  → modality→quantity x ＝ modality→quantity y
  → x ＝ y
modality-ext {modality r₁ q₁} {modality r₂ q₂} u v = ap² modality u v

arg-info-ext
  : {x y : Arg-info}
  → arg-vis x ＝ arg-vis y
  → arg-modality x ＝ arg-modality y
  → x ＝ y
arg-info-ext {arg-info v₁ m₁} {arg-info v₂ m₂} p q = ap² arg-info p q

arg-ext
  : {x y : Arg A}
  → unai x ＝ unai y
  → unarg x ＝ unarg y
  → x ＝ y
arg-ext {x = arg i₁ x} {arg i₂ y} p q = ap² arg p q


-- wtf agda?
private module N where primitive
  primQNameToWord64sInjective : ∀ x y → name→words64 x ＝ⁱ name→words64 y → x ＝ⁱ y

open N
  public
  renaming ( primQNameToWord64sInjective to name→words64-injⁱ )

name→words64-inj : {a b : Name} → name→words64 a ＝ name→words64 b → a ＝ b
name→words64-inj = Id≃path.to ∘ name→words64-injⁱ _ _ ∘ Id≃path.from
