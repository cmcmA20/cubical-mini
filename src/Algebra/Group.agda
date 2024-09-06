{-# OPTIONS --safe #-}
module Algebra.Group where

open import Cat.Prelude

open import Algebra.Monoid public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  e x y : A
  _✦_ : A → A → A
  n : HLevel

-- groups

record is-group {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field
    inverse : A → A
    has-monoid : is-monoid _⋆_
  open is-monoid has-monoid public

  field
    inverse-l : Invertibility-lᵘ A id inverse _⋆_
    inverse-r : Invertibility-rᵘ A id inverse _⋆_

  instance
    Symᵘ-is-group : Symᵘ A
    Symᵘ-is-group .minv = inverse

unquoteDecl is-group-iso = declare-record-iso is-group-iso (quote is-group)

opaque
  is-group-is-prop : {_✦_ : A → A → A} → is-prop (is-group _✦_)
  is-group-is-prop {A} {_✦_} M N = Equiv.injective (≅ₜ→≃ is-group-iso)
    $  fun-ext (λ a → monoid-inverse-unique {IM = M .is-group.has-monoid} a _ _
         (M .is-group.inverse-l a) (N .is-group.inverse-r a ∙ sym u))
    ,ₚ prop!
    where
      u : M .is-group.id ＝ N .is-group.id
      u = identity-unique (is-monoid.has-unital-magma (M .is-group.has-monoid))
                          (is-monoid.has-unital-magma (N .is-group.has-monoid))
      instance
        A-set : H-Level 2 A
        A-set = hlevel-basic-instance 2 (M .is-group.has-is-of-hlevel)

instance
  H-Level-is-group : ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-group _✦_)
  H-Level-is-group ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-group-is-prop


record Group-on {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    _⋆_ : X → X → X
    has-group : is-group _⋆_

  open is-group has-group public
  infixr 20 _⋆_

unquoteDecl group-on-iso = declare-record-iso group-on-iso (quote Group-on)

opaque
  group-on-is-set : is-set (Group-on A)
  group-on-is-set = ≅→is-of-hlevel 2 group-on-iso λ (op , x) _ _ _ →
    let open is-group x in prop!


record Group-hom
  {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (e : A → B)
  (M : Group-on A) (M′ : Group-on B) : 𝒰 (ℓ ⊔ ℓ′)
  where
    no-eta-equality
    private
      module A = Group-on M
      module B = Group-on M′

    field pres-⋆  : (x y : A) → e (x ∙ y) ＝ e x ∙ e y

    pres-id : e A.id ＝ B.id
    pres-id =
      e A.id                           ~⟨ B.id-r _ ⟨
      e A.id ∙ B.id                    ~⟨ e A.id ◁ B.inverse-r (e A.id) ⟨
      e A.id ∙ (e A.id ∙ e A.id ⁻¹)    ~⟨ B.assoc _ _ _ ⟩
      ⌜ e A.id ∙ e A.id ⌝ ∙ e A.id ⁻¹  ~⟨ ap! (pres-⋆ A.id A.id ⁻¹ ∙ ap e (A.id-l _)) ⟩
      e A.id ∙ e A.id ⁻¹               ~⟨ B.inverse-r _ ⟩
      B.id                             ∎

    pres-inv : (x : A) → e (x ⁻¹) ＝ (e x) ⁻¹
    pres-inv x = monoid-inverse-unique {IM = B.has-monoid} (e x) _ _
      (sym (pres-⋆ _ _) ∙∙ ap e (A.inverse-l _) ∙∙ pres-id)
      (B.inverse-r _)

unquoteDecl group-hom-iso = declare-record-iso group-hom-iso (quote Group-hom)

opaque
  group-hom-is-prop : ∀ {M : Group-on A} {M′ : Group-on B} {f}
                    → is-prop (Group-hom f M M′)
  group-hom-is-prop {M′} = ≅→is-of-hlevel! 1 group-hom-iso where
    open Group-on M′

instance opaque
  H-Level-group-on : ⦃ n ≥ʰ 2 ⦄ → H-Level n (Group-on A)
  H-Level-group-on ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 group-on-is-set

  H-Level-group-hom : ⦃ n ≥ʰ 1 ⦄ → ∀ {M : Group-on A} {M′ : Group-on B} {f}
                    → H-Level n (Group-hom f M M′)
  H-Level-group-hom ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance group-hom-is-prop

instance
  ⇒-Group : ⇒-notation (Σ[ X ꞉ Set ℓ ] Group-on ⌞ X ⌟) (Σ[ Y ꞉ Set ℓ′ ] Group-on ⌞ Y ⌟) (𝒰 (ℓ ⊔ ℓ′))
  ⇒-Group ._⇒_ (A , X) (B , Y) = Total-hom (λ P Q → ⌞ P ⌟ → ⌞ Q ⌟) Group-hom {a = A} {b = B} X Y

  Refl-Group-hom : Refl {A = Group-on A} (Group-hom refl)
  Refl-Group-hom .refl .Group-hom.pres-⋆ _ _ = refl

  Trans-Group-hom
    : {f : A → B} {g : B → C}
    → Trans (Group-hom f) (Group-hom g) (Group-hom (f ∙ g))
  Trans-Group-hom {f} {g} ._∙_ p q .Group-hom.pres-⋆ a a′ =
    ap g (p .Group-hom.pres-⋆ a a′) ∙ q .Group-hom.pres-⋆ (f a) (f a′)

group-on↪monoid-on : Group-on A ↪ₜ Monoid-on A
group-on↪monoid-on .fst G .Monoid-on._⋆_ = G .Group-on._⋆_
group-on↪monoid-on .fst G .Monoid-on.has-monoid = G .Group-on.has-monoid
group-on↪monoid-on .snd = set-injective→is-embedding! λ {x} {y} p →
  Equiv.injective (≅ₜ→≃ group-on-iso) $ ap Monoid-on._⋆_ p ,ₚ prop!


record make-group {ℓ} (X : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field
    group-is-set : is-set X
    id  : X
    _⋆_ : X → X → X
    inverse : X → X
    id-l      : Unitality-lᵘ X id _⋆_
    inverse-l : Invertibility-lᵘ X id inverse _⋆_
    assoc     : Associativityᵘ X _⋆_

  private instance
    Reflᵘ-make-group : Reflᵘ X
    Reflᵘ-make-group .mempty = id

    Symᵘ-make-group : Symᵘ X
    Symᵘ-make-group .minv = inverse

    Transᵘ-make-group : Transᵘ X
    Transᵘ-make-group ._<>_ = _⋆_

  inverse-r : Invertibility-rᵘ X id inverse _⋆_
  inverse-r x =
    x ∙ x ⁻¹                       ~⟨ id-l _ ⟨
    id ∙ (x ∙ x ⁻¹)                ~⟨ inverse-l (x ⁻¹) ▷ _ ⟨
    (x ⁻¹ ⁻¹ ∙ x ⁻¹) ∙ (x ∙ x ⁻¹)  ~⟨ assoc _ _ _ ⟨
    x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ (x ∙ x ⁻¹))  ~⟨ _ ◁ assoc (x ⁻¹) x (x ⁻¹) ⟩
    x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ x) ∙ x ⁻¹    ~⟨ (x ⁻¹ ⁻¹) ◁ inverse-l x ▷ (x ⁻¹) ⟩
    x ⁻¹ ⁻¹ ∙ (id ∙ x ⁻¹)          ~⟨ _ ◁ id-l (x ⁻¹) ⟩
    x ⁻¹ ⁻¹ ∙ x ⁻¹                 ~⟨ inverse-l _ ⟩
    id                             ∎

  id-r : Unitality-rᵘ X id _⋆_
  id-r x =
    x ∙ id          ~⟨ x ◁ inverse-l _ ⟨
    x ∙ (x ⁻¹ ∙ x)  ~⟨ assoc _ _ _ ⟩
    (x ∙ x ⁻¹) ∙ x  ~⟨ inverse-r _ ▷ x ⟩
    id ∙ x          ~⟨ id-l _ ⟩
    x               ∎

  to-is-group : is-group _⋆_
  to-is-group .is-group.has-monoid = to-is-monoid m where
    m : make-monoid X
    m .make-monoid.monoid-is-set = group-is-set
    m .make-monoid.id = id
    m .make-monoid._⋆_ = _⋆_
    m .make-monoid.id-l = id-l
    m .make-monoid.id-r = id-r
    m .make-monoid.assoc = assoc
  to-is-group .is-group.inverse = inverse
  to-is-group .is-group.inverse-l = inverse-l
  to-is-group .is-group.inverse-r = inverse-r

  to-group-on : Group-on X
  to-group-on .Group-on._⋆_ = _⋆_
  to-group-on .Group-on.has-group = to-is-group

open make-group using (to-is-group ; to-group-on) public
