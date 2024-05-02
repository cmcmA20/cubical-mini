{-# OPTIONS --safe #-}
module Algebra.Magma where

open import Categories.Prelude

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  _✦_ : A → A → A
  n : HLevel

-- untruncated magmas

record ∞-Magma-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field _⋆_ : X → X → X
  infixr 20 _⋆_

  instance
    Transitiveᵘ-∞-Magma-on : Transitiveᵘ X
    Transitiveᵘ-∞-Magma-on ._<>_ = _⋆_

record ∞-magma-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  (M : ∞-Magma-on A) (M′ : ∞-Magma-on B) (e : A → B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = ∞-Magma-on M
      module B = ∞-Magma-on M′

    field pres-⋆ : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

∞-Magma[_⇒_]
  : (A : Σ[ X ꞉ 𝒰 ℓ ] ∞-Magma-on X) (B : Σ[ X ꞉ 𝒰 ℓ′ ] ∞-Magma-on X) → 𝒰 (ℓ ⊔ ℓ′)
∞-Magma[ A ⇒ B ] = Σ[ f ꞉ A →̇ B ] ∞-magma-hom (A .snd) (B .snd) f

∞-Magma≃
  : {ℓ ℓ′ : Level} (A : Σ[ X ꞉ 𝒰 ℓ ] ∞-Magma-on X) (B : Σ[ X ꞉ 𝒰 ℓ′ ] ∞-Magma-on X)
    (e : ⌞ A ⌟ ≃ ⌞ B ⌟) → 𝒰 (ℓ ⊔ ℓ′)
∞-Magma≃ A B (f , _) = ∞-magma-hom (A .snd) (B .snd) f


-- n-truncated magmas

record is-n-magma (n : HLevel) {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-is-of-hlevel : is-of-hlevel n A

  instance
    H-Level-magma-carrier : H-Level n A
    H-Level-magma-carrier .H-Level.has-of-hlevel = has-is-of-hlevel

    Transitiveᵘ-is-n-magma : Transitiveᵘ A
    Transitiveᵘ-is-n-magma ._<>_ = _⋆_

unquoteDecl is-n-magma-iso = declare-record-iso is-n-magma-iso (quote is-n-magma)

is-magma is-2-magma : (A → A → A) → 𝒰 _
is-magma = is-n-magma 2
is-2-magma = is-n-magma 3

opaque
  is-n-magma-is-prop : is-prop (is-n-magma n _✦_)
  is-n-magma-is-prop {n} = ≅→is-of-hlevel 1 is-n-magma-iso (is-of-hlevel-is-prop n)

instance opaque
  H-Level-n-magma : ∀ {k} → H-Level (suc k) (is-n-magma n _✦_)
  H-Level-n-magma = hlevel-prop-instance is-n-magma-is-prop

module _ (n : HLevel) where
  record n-Magma-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
    no-eta-equality
    field
      _⋆_ : X → X → X
      has-n-magma : is-n-magma n _⋆_

    open is-n-magma has-n-magma public
    infixr 20 _⋆_

  unquoteDecl n-magma-on-iso = declare-record-iso n-magma-on-iso (quote n-Magma-on)

  record n-Magma-hom
    {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
    (M : n-Magma-on A) (M′ : n-Magma-on B) (e : A → B) : 𝒰 (ℓ ⊔ ℓ′)
    where
      no-eta-equality
      private
        module A = n-Magma-on M
        module B = n-Magma-on M′

      field pres-⋆ : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

  unquoteDecl n-magma-hom-iso = declare-record-iso n-magma-hom-iso (quote n-Magma-hom)

Magma-on = n-Magma-on 2
2-Magma-on = n-Magma-on 3

-- TODO generalize
opaque
  magma-on-is-set : is-set (Magma-on A)
  magma-on-is-set M = ≅→is-of-hlevel! 2 (n-magma-on-iso 2) M where
    open n-Magma-on M

n-magma-hom-is-of-hlevel : ∀ {M : n-Magma-on (suc n) A} {M′ : n-Magma-on (suc n) B} {f}
                         → is-of-hlevel n (n-Magma-hom (suc n) M M′ f)
n-magma-hom-is-of-hlevel {M′} = ≅→is-of-hlevel! _ (n-magma-hom-iso _) where
  open n-Magma-on M′

instance opaque
  H-Level-magma-on : H-Level (2 + n) (Magma-on A)
  H-Level-magma-on = hlevel-basic-instance 2 magma-on-is-set

  H-Level-n-magma-hom : ∀ {M : n-Magma-on (suc n) A} {M′ : n-Magma-on (suc n) B} {f}
                      → H-Level n (n-Magma-hom (suc n) M M′ f)
  H-Level-n-magma-hom .H-Level.has-of-hlevel = n-magma-hom-is-of-hlevel
