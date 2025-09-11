{-# OPTIONS --safe #-}
module Order.Diagram.Glb where

open import Meta.Effect

open import Cat.Prelude

open import Order.Base
open import Order.Morphism
open import Functions.Surjection

private variable o o′ ℓ ℓ′ ℓᵢ : Level

module _ (P : Poset o ℓ) where
  open Poset P

  record is-glb {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) (glb : Ob)
          : Type (o ⊔ ℓ ⊔ ℓᵢ) where
    no-eta-equality
    field
      glb≤fam  : ∀ i → glb ≤ F i
      greatest : (lb′ : Ob) → (∀ i → lb′ ≤ F i) → lb′ ≤ glb

  record Glb {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) : Type (o ⊔ ℓ ⊔ ℓᵢ) where
    no-eta-equality
    field
      glb     : Ob
      has-glb : is-glb F glb
    open is-glb has-glb public

unquoteDecl H-Level-is-glb = declare-record-hlevel 1 H-Level-is-glb (quote is-glb)
unquoteDecl Glb-Iso = declare-record-iso Glb-Iso (quote Glb)

Has-glbs-of-size : Poset o ℓ → (ℓ′ : Level) → Type (o ⊔ ℓ ⊔ ℓsuc ℓ′)
Has-glbs-of-size P ℓ′ = {I : Type ℓ′} {F : I → ⌞ P ⌟} → Glb P F

module _ {P : Poset o ℓ} where
  open Poset P
  open is-glb

  glb-unique
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {x y}
    → is-glb P F x → is-glb P F y
    → x ＝ y
  glb-unique is is′ = ≤-antisym
    (is′ .greatest _ (is .glb≤fam))
    (is .greatest _ (is′ .glb≤fam))

  Glb-is-prop
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob}
    → is-prop (Glb P F)
  Glb-is-prop = ≅→is-of-hlevel 1 Glb-Iso λ x y → glb-unique (x .snd) (y .snd) ,ₚ prop!

  instance opaque
    H-Level-Glb
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (Glb P F)
    H-Level-Glb ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Glb-is-prop

  lift-is-glb
    : ∀ {ℓᵢ ℓᵢ′} {I : Type ℓᵢ} {F : I → Ob} {glb}
    → is-glb P F glb → is-glb P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′}) glb
  lift-is-glb is .glb≤fam (lift ix) = is .glb≤fam ix
  lift-is-glb is .greatest ub′ le = is .greatest ub′ (le ∘ₜ lift)

  lift-glb
    : ∀ {ℓᵢ ℓᵢ′} {I : Type ℓᵢ} {F : I → Ob}
    → Glb P F → Glb P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′})
  lift-glb glb .Glb.glb = Glb.glb glb
  lift-glb glb .Glb.has-glb = lift-is-glb (Glb.has-glb glb)

  lower-is-glb
    : ∀ {ℓᵢ ℓᵢ′} {I : Type ℓᵢ} {F : I → Ob} {glb}
    → is-glb P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′}) glb → is-glb P F glb
  lower-is-glb is .glb≤fam ix = is .glb≤fam (lift ix)
  lower-is-glb is .greatest ub′ le = is .greatest ub′ (le ∘ₜ Lift.lower)

  lower-glb
    : ∀ {ℓᵢ ℓᵢ′} {I : Type ℓᵢ} {F : I → Ob}
    → Glb P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′}) → Glb P F
  lower-glb glb .Glb.glb = Glb.glb glb
  lower-glb glb .Glb.has-glb = lower-is-glb (Glb.has-glb glb)

  module _
    {ℓᵢ ℓᵢ′} {Ix : Type ℓᵢ} {Im : Type ℓᵢ′}
    {F : Im → Ob} where
    module _ (f : Ix ↠ Im) where
      cover-preserves-is-glb : ∀ {glb} → is-glb P F glb → is-glb P (F ∘ₜ (f $_)) glb
      cover-preserves-is-glb g .glb≤fam i = g .glb≤fam (f $ i)
      cover-preserves-is-glb g .greatest lb′ le = g .greatest lb′ λ i → ∥-∥₁.proj! do
        i′ , p ← f .snd i
        pure (le i′ ∙ =→≤ (ap F p))

      cover-preserves-glb : Glb P F → Glb P (F ∘ₜ (f $_))
      cover-preserves-glb g .Glb.glb = _
      cover-preserves-glb g .Glb.has-glb = cover-preserves-is-glb (g .Glb.has-glb)

      cover-reflects-is-glb : ∀ {glb} → is-glb P (F ∘ₜ (f $_)) glb → is-glb P F glb
      cover-reflects-is-glb g .glb≤fam i = ∥-∥₁.proj! do
        y , p ← f .snd i
        pure (g .glb≤fam y ∙ =→≤ (ap F p))
      cover-reflects-is-glb g .greatest lb′ le = g .greatest lb′ λ i → le (f $  i)

      cover-reflects-glb : Glb P (F ∘ₜ (f $_)) → Glb P F
      cover-reflects-glb g .Glb.glb = _
      cover-reflects-glb g .Glb.has-glb = cover-reflects-is-glb (g .Glb.has-glb)

      cover-reindexing : (s s′ : Ob) → is-glb P F s → is-glb P (F ∘ₜ (f $_)) s′ → s ＝ s′
      cover-reindexing s s′ g g′ = ≤-antisym
          (greatest g′ s λ t′ → glb≤fam g (f $ t′))
          (greatest g s′ λ t → elim! (λ x p → subst (λ φ → s′ ≤ F φ) p (glb≤fam g′ x)) (f .snd t))

    module _ (f : Ix ≃ Im) where
      equiv-reindexing : (s s′ : Ob) → is-glb P F s → is-glb P (F ∘ₜ (f $_)) s′ → s ＝ s′
      equiv-reindexing = cover-reindexing (≃→↠ f)

  cast-is-glb
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {I′ : 𝒰 ℓᵢ′} {F : I → Ob} {G : I′ → Ob} {glb}
    → (e : I ≃ I′)
    → (∀ i → F i ＝ G (e $ i))
    → is-glb P F glb
    → is-glb P G glb
  cast-is-glb {G} e p has-glb .glb≤fam i′ =
      has-glb .glb≤fam (e ⁻¹ $ i′)
    ∙ =→~ (p (e ⁻¹ $ i′) ∙ ap G (Equiv.ε e # i′))
  cast-is-glb     e p has-glb .greatest lb lb≤G =
    has-glb .greatest lb λ i → lb≤G (e $ i) ∙ =→~⁻ (p i)

  cast-glb
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {I′ : 𝒰 ℓᵢ′} {F : I → Ob} {G : I′ → Ob}
    → (e : I ≃ I′)
    → (∀ i → F i ＝ G (e $ i))
    → Glb P F
    → Glb P G
  cast-glb e p g .Glb.glb     = g .Glb.glb
  cast-glb e p g .Glb.has-glb = cast-is-glb e p (g .Glb.has-glb)

  cast-is-glbᶠ
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F G : I → Ob} {glb}
    → (∀ i → F i ＝ G i)
    → is-glb P F glb
    → is-glb P G glb
  cast-is-glbᶠ = cast-is-glb refl

  fam-bound→is-glb
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → (i : I) → (∀ j → F i ≤ F j)
    → is-glb P F (F i)
  fam-bound→is-glb i le .glb≤fam       = le
  fam-bound→is-glb i le .greatest y ge = ge i

  glb-of-const-fam
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x}
    → (∀ i j → F i ＝ F j)
    → is-glb P F x
    → ∀ i → F i ＝ x
  glb-of-const-fam {F = F} is-const x-glb i =
    ≤-antisym
      (greatest x-glb (F i) λ j → =→~ (is-const i j))
      (glb≤fam x-glb i)

  const-inhabited-fam→is-glb
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x}
    → (∀ i → F i ＝ x)
    → ∥ I ∥₁
    → is-glb P F x
  const-inhabited-fam→is-glb {I} {F} {x} is-const =
    rec! mk-is-glb where
      mk-is-glb : I → is-glb P F x
      mk-is-glb i .is-glb.glb≤fam j = =→~⁻ (is-const j)
      mk-is-glb i .is-glb.greatest y ge =
        y   ≤⟨ ge i ⟩
        F i =⟨ is-const i ⟩
        x   ∎

  const-inhabited-fam→glb
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → (∀ i j → F i ＝ F j)
    → ∥ I ∥₁
    → Glb P F
  const-inhabited-fam→glb {I} {F} is-const =
    rec! mk-glb where
      mk-glb : I → Glb P F
      mk-glb i .Glb.glb = F i
      mk-glb i .Glb.has-glb =
        const-inhabited-fam→is-glb (λ j → is-const j i) ∣ i ∣₁


module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} {I : 𝒰 ℓᵢ} {F : I → ⌞ Q ⌟} where
  private
    module P = Poset P
    module Q = Poset Q

  module _ {L : P ⇒ Q} {R : Q ⇒ P} (gc : L ⊣ R) where
    open Adjoint gc
    adjoint-r→is-glb : {x : ⌞ Q ⌟} → is-glb Q F x → is-glb P (F ∙ R #_) (R # x)
    adjoint-r→is-glb {x} g .is-glb.glb≤fam i = R # (g .is-glb.glb≤fam i)
    adjoint-r→is-glb {x} g .is-glb.greatest lb′ f =
      adjunct-l (g .is-glb.greatest (L # lb′) λ i → adjunct-r (f i))

    adjoint-r→Glb : Glb Q F → Glb P (F ∙ R #_)
    adjoint-r→Glb g .Glb.glb = R # (g .Glb.glb)
    adjoint-r→Glb g .Glb.has-glb = adjoint-r→is-glb (g .Glb.has-glb)

  module _ (e : P ≅ Q) where
    ≅→is-glb⁻ : {x : ⌞ Q ⌟} → is-glb Q F x → is-glb P (F ∙ (e ⁻¹) #_) ((e ⁻¹) # x)
    ≅→is-glb⁻ = adjoint-r→is-glb (≅ₚ→⊣ e)

    ≅→Glb⁻ : Glb Q F → Glb P (F ∙ (e ⁻¹) #_)
    ≅→Glb⁻ = adjoint-r→Glb (≅ₚ→⊣ e)

module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} {I : 𝒰 ℓᵢ} {F : I → ⌞ P ⌟} (e : P ≅ Q) where
  private
    module P = Poset P
    module Q = Poset Q
    e⁻¹ : Q ≅ P
    e⁻¹ = e ⁻¹
    module A = Adjoint (≅ₚ→⊣ e⁻¹)
    module B = Adjoint (≅ₚ→⊣ e)
  open Iso

  ≅→is-glb : {x : ⌞ P ⌟} → is-glb Q (F ∙ e #_) (e # x) → is-glb P F x
  ≅→is-glb {x} g .is-glb.glb≤fam i =
    B.η # x ∙ (e .from # g .is-glb.glb≤fam i) ∙ A.ε # F i
  ≅→is-glb {x} g .is-glb.greatest lb′ f =
      B.η # lb′
    ∙ e .from # g .is-glb.greatest (e .to # lb′) (λ i → e .to $ f i)
    ∙ A.ε # x

  ≅→Glb : Glb Q (F ∙ e #_) → Glb P F
  ≅→Glb g .Glb.glb = e .from # g .Glb.glb
  ≅→Glb g .Glb.has-glb = ≅→is-glb (subst (is-glb Q _) (sym (e .inv-o #ₚ _)) (g .Glb.has-glb))
