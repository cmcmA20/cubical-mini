{-# OPTIONS --safe #-}
module Algebra.Magma.Unital where

open import Cat.Prelude

open import Algebra.Magma public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  e x y z : A
  _✦_ : A → A → A
  n : HLevel

-- unital magmas

record is-unital-magma {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-magma : is-magma _⋆_
  open is-n-magma has-magma public

  field
    id   : A
    id-l : Π[ Unitality-l A id _⋆_ ]
    id-r : Π[ Unitality-r A id _⋆_ ]

  instance
    Pointed-is-unital-magma : Pointed A
    Pointed-is-unital-magma .mempty = id

unquoteDecl is-unital-magma-iso = declare-record-iso is-unital-magma-iso (quote is-unital-magma)

module _ where
  open is-unital-magma

  identity-unique
    : (M M′ : is-unital-magma _✦_)
    → M .id ＝ M′ .id
  identity-unique {_✦_} M M′ =
    M .id           ~⟨ is-unital-magma.id-r M′ _ ⟨
    M .id ✦ M′ .id  ~⟨ is-unital-magma.id-l M _  ⟩
    M′ .id          ∎

opaque
  is-unital-magma-is-prop : is-prop (is-unital-magma _✦_)
  is-unital-magma-is-prop C C′ = Equiv.injective (≅ₜ→≃ is-unital-magma-iso) $
    prop! ,ₚ identity-unique C C′ ,ₚ prop!
    where open is-unital-magma C

instance opaque
  H-Level-is-unital-magma : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-unital-magma _✦_)
  H-Level-is-unital-magma ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-unital-magma-is-prop


record UMagma-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-unital-magma : is-unital-magma _⋆_

  open is-unital-magma has-unital-magma public
  infixr 20 _⋆_

unquoteDecl umagma-on-iso = declare-record-iso umagma-on-iso (quote UMagma-on)

opaque
  umagma-on-is-set : is-set (UMagma-on A)
  umagma-on-is-set = ≅→is-of-hlevel 2 umagma-on-iso $ λ (_ , x) _ _ _ →
    let open is-unital-magma x in prop!

instance opaque
  H-Level-umagma-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (UMagma-on A)
  H-Level-umagma-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 umagma-on-is-set


record UMagma-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (e : A → B)
  (M : UMagma-on A) (M′ : UMagma-on B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = UMagma-on M
      module B = UMagma-on M′

    field
      pres-id : e refl ＝ refl
      pres-⋆  : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

unquoteDecl umagma-hom-iso = declare-record-iso umagma-hom-iso (quote UMagma-hom)

opaque
  umagma-hom-is-prop : ∀ {M : UMagma-on A} {M′ : UMagma-on B} {f}
                     → is-prop (UMagma-hom f M M′)
  umagma-hom-is-prop {M′} = ≅→is-of-hlevel! 1 umagma-hom-iso where
    open UMagma-on M′

instance opaque
  H-Level-umagma-hom : ⦃ n ≥ʰ 1 ⦄ → ∀ {M : UMagma-on A} {M′ : UMagma-on B} {f}
                     → H-Level n (UMagma-hom f M M′)
  H-Level-umagma-hom ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance umagma-hom-is-prop

instance
  ⇒-UMagma : ⇒-notation (Σ[ X ꞉ Set ℓ ] UMagma-on ⌞ X ⌟) (Σ[ Y ꞉ Set ℓ′ ] UMagma-on ⌞ Y ⌟) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-UMagma ._⇒_ (A , X) (B , Y) = Total-hom (λ P Q → ⌞ P ⌟ → ⌞ Q ⌟) UMagma-hom {a = A} {b = B} X Y

  Refl-UMagma-hom : Refl {A = UMagma-on A} (UMagma-hom refl)
  Refl-UMagma-hom .refl .UMagma-hom.pres-⋆ _ _ = refl
  Refl-UMagma-hom .refl .UMagma-hom.pres-id = refl

  Comp-UMagma-hom
    : {f : A → B} {g : B → C}
    → Comp (UMagma-hom f) (UMagma-hom g) (UMagma-hom (f ∙ g))
  Comp-UMagma-hom {f} {g} ._∙_ p q .UMagma-hom.pres-⋆ a a′ =
    ap g (p .UMagma-hom.pres-⋆ a a′) ∙ q .UMagma-hom.pres-⋆ (f a) (f a′)
  Comp-UMagma-hom {f} {g} ._∙_ p q .UMagma-hom.pres-id =
    ap g (p .UMagma-hom.pres-id) ∙ q .UMagma-hom.pres-id

unital-magma-on↪magma-on : UMagma-on A ↪ₜ Magma-on A
unital-magma-on↪magma-on .fst M .n-Magma-on._⋆_ = M .UMagma-on._⋆_
unital-magma-on↪magma-on .fst M .n-Magma-on.has-n-magma = M .UMagma-on.has-magma
unital-magma-on↪magma-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ umagma-on-iso) $ ap n-Magma-on._⋆_ p ,ₚ prop!


record make-unital-magma {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    unital-magma-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    id-l  : Π[ Unitality-l X id _⋆_ ]
    id-r  : Π[ Unitality-r X id _⋆_ ]

  to-is-unital-magma : is-unital-magma _⋆_
  to-is-unital-magma .is-unital-magma.has-magma .is-n-magma.has-is-of-hlevel =
    unital-magma-is-set
  to-is-unital-magma .is-unital-magma.id = id
  to-is-unital-magma .is-unital-magma.id-l = id-l
  to-is-unital-magma .is-unital-magma.id-r = id-r

  to-unital-magma-on : UMagma-on X
  to-unital-magma-on .UMagma-on._⋆_ = _⋆_
  to-unital-magma-on .UMagma-on.has-unital-magma = to-is-unital-magma

open make-unital-magma using (to-is-unital-magma ; to-unital-magma-on) public
