{-# OPTIONS --safe #-}
module Algebra.Monoid where

open import Cat.Prelude

open import Algebra.Magma.Unital public
open import Algebra.Semigroup public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  e x y : A
  _✦_ : A → A → A
  n : HLevel

-- monoids

record is-monoid {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field has-semigroup : is-semigroup _⋆_
  open is-semigroup has-semigroup public

  field
    id   : A
    id-l : Π[ Unitality-l A id _⋆_ ]
    id-r : Π[ Unitality-r A id _⋆_ ]

  instance
    Pointed-is-monoid : Pointed A
    Pointed-is-monoid .mempty = id

    Unit-l-monoid : Unit-l A
    Unit-l-monoid .<>-id-l = id-l

    Unit-r-monoid : Unit-r A
    Unit-r-monoid .<>-id-r = id-r

  has-unital-magma : is-unital-magma _⋆_
  has-unital-magma .is-unital-magma.has-magma = has-magma
  has-unital-magma .is-unital-magma.id = id
  has-unital-magma .is-unital-magma.id-l = id-l
  has-unital-magma .is-unital-magma.id-r = id-r

unquoteDecl is-monoid-iso = declare-record-iso is-monoid-iso (quote is-monoid)

opaque
  is-monoid-is-prop : is-prop (is-monoid _✦_)
  is-monoid-is-prop M M′ = Equiv.injective (≅ₜ→≃ is-monoid-iso) $
    prop! ,ₚ identity-unique (is-monoid.has-unital-magma M) (is-monoid.has-unital-magma M′) ,ₚ prop!
    where open is-monoid M

instance opaque
  H-Level-is-monoid : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-monoid _✦_)
  H-Level-is-monoid ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-monoid-is-prop

module _ {_✦_ : A → A → A} {IM : is-monoid _✦_} where
  open is-monoid IM
  monoid-inverse-unique : (e x y : A) → x ∙ e ＝ refl → e ∙ y ＝ refl → x ＝ y
  monoid-inverse-unique e x y p q =
    x              ~⟨ id-r _ ⟨
    x ∙ ⌜ refl ⌝   ~⟨ ap¡ q ⟨
    x ∙ (e ∙ y)    ~⟨ assoc _ _ _ ⟩
    ⌜ x ∙ e ⌝ ∙ y  ~⟨ ap! p ⟩
    refl ∙ y       ~⟨ id-l _ ⟩
    y              ∎


record Monoid-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-monoid : is-monoid _⋆_

  open is-monoid has-monoid public
  infixr 20 _⋆_

unquoteDecl monoid-on-iso = declare-record-iso monoid-on-iso (quote Monoid-on)

opaque
  monoid-on-is-set : is-set (Monoid-on A)
  monoid-on-is-set = ≅→is-of-hlevel 2 monoid-on-iso λ (_ , x) _ _ _ →
    let open is-monoid x in prop!


record Monoid-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (e : A → B)
  (M : Monoid-on A) (M′ : Monoid-on B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = Monoid-on M
      module B = Monoid-on M′

    field
      pres-id : e refl ＝ refl
      pres-⋆  : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

unquoteDecl monoid-hom-iso = declare-record-iso monoid-hom-iso (quote Monoid-hom)

opaque
  monoid-hom-is-prop : ∀ {M : Monoid-on A} {M′ : Monoid-on B} {f}
                     → is-prop (Monoid-hom f M M′)
  monoid-hom-is-prop {M′} = ≅→is-of-hlevel! 1 monoid-hom-iso where open Monoid-on M′

instance opaque
  H-Level-monoid-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (Monoid-on A)
  H-Level-monoid-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 monoid-on-is-set

  H-Level-monoid-hom : ⦃ n ≥ʰ 1 ⦄ → ∀ {M : Monoid-on A} {M′ : Monoid-on B} {f}
                     → H-Level n (Monoid-hom f M M′)
  H-Level-monoid-hom ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance monoid-hom-is-prop

instance
  ⇒-Monoid : ⇒-notation (Σ[ X ꞉ Type ℓ ] Monoid-on X) (Σ[ Y ꞉ Type ℓ′ ] Monoid-on Y) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-Monoid .⇒-notation.Constraint _ _ = ⊤
  ⇒-Monoid ._⇒_ (A , X) (B , Y) = Total-hom Fun Monoid-hom X Y

  Refl-Monoid-hom : Refl {A = Monoid-on A} (Monoid-hom refl)
  Refl-Monoid-hom .refl .Monoid-hom.pres-⋆ _ _ = refl
  Refl-Monoid-hom .refl .Monoid-hom.pres-id = refl

  Comp-Monoid-hom
    : {f : A → B} {g : B → C}
    → Comp (Monoid-hom f) (Monoid-hom g) (Monoid-hom (f ∙ g))
  Comp-Monoid-hom {f} {g} ._∙_ p q .Monoid-hom.pres-⋆ a a′ =
    ap g (p .Monoid-hom.pres-⋆ a a′) ∙ q .Monoid-hom.pres-⋆ (f a) (f a′)
  Comp-Monoid-hom {f} {g} ._∙_ p q .Monoid-hom.pres-id =
    ap g (p .Monoid-hom.pres-id) ∙ q .Monoid-hom.pres-id

monoid-on↪semigroup-on : Monoid-on A ↪ₜ Semigroup-on A
monoid-on↪semigroup-on .fst M .Semigroup-on._⋆_ = M .Monoid-on._⋆_
monoid-on↪semigroup-on .fst M .Semigroup-on.has-semigroup =
  M .Monoid-on.has-monoid .is-monoid.has-semigroup
monoid-on↪semigroup-on .snd = set-injective→is-embedding! λ p →
  Equiv.injective (≅ₜ→≃ monoid-on-iso) $ ap Semigroup-on._⋆_ p ,ₚ prop!

monoid-on↪unital-magma-on : Monoid-on A ↪ₜ UMagma-on A
monoid-on↪unital-magma-on .fst M .UMagma-on._⋆_ = M .Monoid-on._⋆_
monoid-on↪unital-magma-on .fst M .UMagma-on.has-unital-magma = Monoid-on.has-unital-magma M
monoid-on↪unital-magma-on .snd = set-injective→is-embedding! λ {x} {y} p →
  Equiv.injective (≅ₜ→≃ monoid-on-iso) $ ap UMagma-on._⋆_ p ,ₚ prop!


record make-monoid {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    monoid-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    id-l : Π[ Unitality-l X id _⋆_ ]
    id-r : Π[ Unitality-r X id _⋆_ ]
    assoc : Π[ Associativity X _⋆_ ]

  to-is-monoid : is-monoid _⋆_
  to-is-monoid .is-monoid.has-semigroup = to-is-semigroup sg where
    sg : make-semigroup X
    sg .make-semigroup.semigroup-is-set = monoid-is-set
    sg .make-semigroup._⋆_ = _⋆_
    sg .make-semigroup.assoc = assoc
  to-is-monoid .is-monoid.id = id
  to-is-monoid .is-monoid.id-l = id-l
  to-is-monoid .is-monoid.id-r = id-r

  to-monoid-on : Monoid-on X
  to-monoid-on .Monoid-on._⋆_ = _⋆_
  to-monoid-on .Monoid-on.has-monoid = to-is-monoid

open make-monoid using (to-is-monoid ; to-monoid-on) public


-- monoid theory
module _ {M : Monoid-on A} where
  open Monoid-on M

  iter-l : ℕ → A → A
  iter-l 0       _ = id
  iter-l (suc n) x = iter-l n x ⋆ x

  iter-r : ℕ → A → A
  iter-r 0       _ = id
  iter-r (suc n) x = x ⋆ iter-r n x

  iter-comm : (n : ℕ) → x ⋆ iter-r n x ＝ iter-r n x ⋆ x
  iter-comm 0       = id-r _ ∙ id-l _ ⁻¹
  iter-comm (suc n) = ap (_ ⋆_) (iter-comm n) ∙ assoc _ _ _

  iter-unique : (n : ℕ) → iter-l n x ＝ iter-r n x
  iter-unique 0       = refl
  iter-unique (suc n) = ap (_⋆ _) (iter-unique n) ∙ iter-comm n ⁻¹
