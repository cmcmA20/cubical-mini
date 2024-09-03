{-# OPTIONS --safe #-}
module Order.Diagram.Glb where

open import Categories.Prelude

open import Order.Base
import Order.Reasoning

private variable o o′ ℓ ℓ′ ℓᵢ : Level

module _ (P : Poset o ℓ) where
  open Order.Reasoning P

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
  open Order.Reasoning P
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

  instance
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
    {f : Ix → Im}
    {F : Im → Ob}
    (surj : is-surjective f)
    where
      cover-preserves-is-glb : ∀ {glb} → is-glb P F glb → is-glb P (F ∘ₜ f) glb
      cover-preserves-is-glb g .glb≤fam i = g .glb≤fam (f i)
      cover-preserves-is-glb g .greatest lb′ le = g .greatest lb′ λ i → ∥-∥₁.proj! do
        (i′ , p) ← surj i
        pure (le i′ ∙ =→≤ (ap F p))

      cover-preserves-glb : Glb P F → Glb P (F ∘ₜ f)
      cover-preserves-glb g .Glb.glb = _
      cover-preserves-glb g .Glb.has-glb = cover-preserves-is-glb (g .Glb.has-glb)

      cover-reflects-is-glb : ∀ {glb} → is-glb P (F ∘ₜ f) glb → is-glb P F glb
      cover-reflects-is-glb g .glb≤fam i = ∥-∥₁.proj! do
        (y , p) ← surj i
        pure (g .glb≤fam y ∙ =→≤ (ap F p))
      cover-reflects-is-glb g .greatest lb′ le = g .greatest lb′ λ i → le (f i)

      cover-reflects-glb : Glb P (F ∘ₜ f) → Glb P F
      cover-reflects-glb g .Glb.glb = _
      cover-reflects-glb g .Glb.has-glb = cover-reflects-is-glb (g .Glb.has-glb)

module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} {I : 𝒰 ℓᵢ} {F : I → ⌞ P ⌟} where
  private
    module P = Poset P
    module Q = Order.Reasoning Q

  open Iso

  ≅→is-glb : (e : P ≅ Q) {x : ⌞ P ⌟}
           → is-glb P F x → is-glb Q (F ∙ e #_) (e # x)
  ≅→is-glb e     g .is-glb.glb≤fam i = e .to # is-glb.glb≤fam g i
  ≅→is-glb e {x} g .is-glb.greatest lb′ f
    = subst (Q._≤ (e # x)) (e .inv-o #ₚ lb′) -- TODO Galois connections
    $ e .to $ g .is-glb.greatest (e .from # lb′) λ i
    → e .from # f i ∙ =→~ (e .inv-i #ₚ F i)

  ≅→Glb : (e : P ≅ Q)
        → Glb P F → Glb Q (F ∙ e #_)
  ≅→Glb e l .Glb.glb = e # l .Glb.glb
  ≅→Glb e l .Glb.has-glb = ≅→is-glb e (l .Glb.has-glb)


module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} {I : 𝒰 ℓᵢ} {F : I → ⌞ Q ⌟} where
  private
    module P = Poset P
    module Q = Order.Reasoning Q
  open Iso

  ≅→is-glb⁻ : (e : P ≅ Q) {y : ⌞ Q ⌟}
            → is-glb P (F ∙ e .from #_) (e .from # y) → is-glb Q F y
  ≅→is-glb⁻ e {y} l = subst² (is-glb Q)
    (fun-ext λ i → e .inv-o #ₚ F i) (e .inv-o #ₚ y)
      (≅→is-glb e l)

  ≅→Glb⁻ : (e : P ≅ Q)
         → Glb P (F ∙ e .from #_) → Glb Q F
  ≅→Glb⁻ e l .Glb.glb = e .to # l .Glb.glb
  ≅→Glb⁻ e l .Glb.has-glb = ≅→is-glb⁻ e $
    subst (is-glb P (F ∙ e .from #_))
      (e .inv-i #ₚ l .Glb.glb ⁻¹)
      (l .Glb.has-glb)
