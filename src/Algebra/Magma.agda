{-# OPTIONS --safe #-}
module Algebra.Magma where

open import Cat.Prelude

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  _✦_ : A → A → A
  n : HLevel

-- untruncated magmas

record ∞-Magma-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field _⋆_ : X → X → X
  infixr 20 _⋆_

  instance
    Has-binary-op-∞-Magma-on : Has-binary-op X
    Has-binary-op-∞-Magma-on ._<>_ = _⋆_

record ∞-magma-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (e : A → B)
  (M : ∞-Magma-on A) (M′ : ∞-Magma-on B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = ∞-Magma-on M
      module B = ∞-Magma-on M′

    field pres-⋆ : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

∞-Magma≃
  : {ℓ ℓ′ : Level} (A : Σ[ X ꞉ 𝒰 ℓ ] ∞-Magma-on X) (B : Σ[ X ꞉ 𝒰 ℓ′ ] ∞-Magma-on X)
    (e : ⌞ A ⌟ ≃ ⌞ B ⌟) → 𝒰 (ℓ ⊔ ℓ′)
∞-Magma≃ A B (f , _) = ∞-magma-hom f (A .snd) (B .snd)

instance
  ⇒-∞-Magma : ⇒-notation (Σ[ X ꞉ 𝒰 ℓ ] ∞-Magma-on X) (Σ[ Y ꞉ 𝒰 ℓ′ ] ∞-Magma-on Y) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-∞-Magma .⇒-notation.Constraint _ _ = ⊤
  ⇒-∞-Magma ._⇒_ X Y = Total-hom Fun ∞-magma-hom (X .snd) (Y .snd)

  Refl-∞-magma-hom : Refl {A = ∞-Magma-on A} (∞-magma-hom refl)
  Refl-∞-magma-hom .refl .∞-magma-hom.pres-⋆ _ _ = refl

  Comp-∞-magma-hom
    : {f : A → B} {g : B → C}
    → Comp (∞-magma-hom f) (∞-magma-hom g) (∞-magma-hom (f ∙ g))
  Comp-∞-magma-hom {f} {g} ._∙_ p q .∞-magma-hom.pres-⋆ a a′ =
    ap g (p .∞-magma-hom.pres-⋆ a a′) ∙ q .∞-magma-hom.pres-⋆ (f a) (f a′)


-- n-truncated magmas

record is-n-magma (n : HLevel) {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-is-of-hlevel : is-of-hlevel n A

  instance
    H-Level-magma-carrier : H-Level n A
    H-Level-magma-carrier .H-Level.has-of-hlevel = has-is-of-hlevel

    Has-binary-op-is-n-magma : Has-binary-op A
    Has-binary-op-is-n-magma ._<>_ = _⋆_

unquoteDecl is-n-magma-iso = declare-record-iso is-n-magma-iso (quote is-n-magma)

is-magma is-2-magma : (A → A → A) → 𝒰 _
is-magma = is-n-magma 2
is-2-magma = is-n-magma 3

opaque
  is-n-magma-is-prop : is-prop (is-n-magma n _✦_)
  is-n-magma-is-prop {n} = ≅→is-of-hlevel 1 is-n-magma-iso (is-of-hlevel-is-prop n)

instance opaque
  H-Level-n-magma : ∀ {k} → ⦃ k ≥ʰ 1 ⦄ → H-Level k (is-n-magma n _✦_)
  H-Level-n-magma ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-n-magma-is-prop

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
    {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (e : A → B)
    (M : n-Magma-on A) (M′ : n-Magma-on B) : 𝒰 (ℓ ⊔ ℓ′)
    where
      no-eta-equality
      private
        module A = n-Magma-on M
        module B = n-Magma-on M′

      field pres-⋆ : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

  unquoteDecl n-magma-hom-iso = declare-record-iso n-magma-hom-iso (quote n-Magma-hom)

Magma-on = n-Magma-on 2
2-Magma-on = n-Magma-on 3

instance
  ⇒-n-Magma : {n : HLevel} → ⇒-notation (Σ[ X ꞉ Set ℓ ] n-Magma-on n ⌞ X ⌟) (Σ[ Y ꞉ Set ℓ′ ] n-Magma-on n ⌞ Y ⌟) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-n-Magma .⇒-notation.Constraint _ _ = ⊤
  ⇒-n-Magma {n} ._⇒_ (A , X) (B , Y) = Total-hom (λ P Q → ⌞ P ⌟ → ⌞ Q ⌟) (n-Magma-hom n) {a = A} {b = B} X Y

  Refl-n-Magma-hom : Refl {A = n-Magma-on n A} (n-Magma-hom n refl)
  Refl-n-Magma-hom .refl .n-Magma-hom.pres-⋆ _ _ = refl

  Comp-n-Magma-hom
    : {f : A → B} {g : B → C}
    → Comp (n-Magma-hom n f) (n-Magma-hom n g) (n-Magma-hom n (f ∙ g))
  Comp-n-Magma-hom {f} {g} ._∙_ p q .n-Magma-hom.pres-⋆ a a′ =
    ap g (p .n-Magma-hom.pres-⋆ a a′) ∙ q .n-Magma-hom.pres-⋆ (f a) (f a′)


-- TODO generalize
opaque
  magma-on-is-set : is-set (Magma-on A)
  magma-on-is-set M = ≅→is-of-hlevel! 2 (n-magma-on-iso 2) M where
    open n-Magma-on M

n-magma-hom-is-of-hlevel : ∀ {M : n-Magma-on (suc n) A} {M′ : n-Magma-on (suc n) B} {f}
                         → is-of-hlevel n (n-Magma-hom (suc n) f M M′)
n-magma-hom-is-of-hlevel {M′} = ≅→is-of-hlevel! _ (n-magma-hom-iso _) where
  open n-Magma-on M′

instance opaque
  H-Level-magma-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (Magma-on A)
  H-Level-magma-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 magma-on-is-set

instance
  H-Level-n-magma-hom : ∀ {M : n-Magma-on (suc n) A} {M′ : n-Magma-on (suc n) B} {f}
                      → H-Level n (n-Magma-hom (suc n) f M M′)
  H-Level-n-magma-hom .H-Level.has-of-hlevel = n-magma-hom-is-of-hlevel
