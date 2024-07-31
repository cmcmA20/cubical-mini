{-# OPTIONS --safe #-}
module Order.Diagram.Lub where

open import Categories.Prelude

open import Order.Base
import Order.Reasoning

module _ {o ℓ} (P : Poset o ℓ) where
  open Poset P

  record is-lub
    {ℓᵢ} {I : 𝒰 ℓᵢ} (F : I → Ob) (lub : Ob)
    : Type (o ⊔ ℓ ⊔ ℓᵢ)
    where
    no-eta-equality
    field
      fam≤lub : ∀ i → F i ≤ lub
      least   : (ub' : Ob) → (∀ i → F i ≤ ub') → lub ≤ ub'

  record Lub {ℓᵢ} {I : 𝒰 ℓᵢ} (F : I → Ob) : 𝒰 (o ⊔ ℓ ⊔ ℓᵢ) where
    no-eta-equality
    field
      lub : Ob
      has-lub : is-lub F lub
    open is-lub has-lub public

unquoteDecl H-Level-is-lub = declare-record-hlevel 1 H-Level-is-lub (quote is-lub)
unquoteDecl lub-iso = declare-record-iso lub-iso (quote Lub)

module _ {o ℓ} {P : Poset o ℓ} where
  open Order.Reasoning P
  open is-lub

  lub-unique
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x y}
    → is-lub P F x → is-lub P F y
    → x ＝ y
  lub-unique {x = x} {y = y} lub lub' = ≤-antisym
    (lub .least y (lub' .fam≤lub))
    (lub' .least x (lub .fam≤lub))

  Lub-is-prop
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → is-prop (Lub P F)
  Lub-is-prop = ≅→is-of-hlevel 1 lub-iso λ x y → lub-unique (x .snd) (y .snd) ,ₚ prop!

  instance
    H-Level-Lub
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (Lub P F)
    H-Level-Lub ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Lub-is-prop

  lift-is-lub
    : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {lub}
    → is-lub P F lub → is-lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ'}) lub
  lift-is-lub is .fam≤lub (lift ix) = is .fam≤lub ix
  lift-is-lub is .least ub' le = is .least ub' (le ∘ₜ lift)

  lift-lub
    : ∀ {ℓᵢ ℓᵢ'} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → Lub P F → Lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ'})
  lift-lub lub .Lub.lub = Lub.lub lub
  lift-lub lub .Lub.has-lub = lift-is-lub (Lub.has-lub lub)

  lower-is-lub
    : ∀ {ℓᵢ ℓᵢ'} {I : 𝒰 ℓᵢ} {F : I → Ob} {lub}
    → is-lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ'}) lub → is-lub P F lub
  lower-is-lub is .fam≤lub ix = is .fam≤lub (lift ix)
  lower-is-lub is .least ub' le = is .least ub' (le ∘ₜ Lift.lower)

  lower-lub
    : ∀ {ℓᵢ ℓᵢ'} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → Lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ'}) → Lub P F
  lower-lub lub .Lub.lub = Lub.lub lub
  lower-lub lub .Lub.has-lub = lower-is-lub (Lub.has-lub lub)

  module _
    {ℓᵢ ℓᵢ'} {Ix : Type ℓᵢ} {Im : Type ℓᵢ'}
    {f : Ix → Im}
    {F : Im → Ob}
    (surj : is-surjective f)
    where
      cover-preserves-is-lub : ∀ {lub} → is-lub P F lub → is-lub P (F ∘ₜ f) lub
      cover-preserves-is-lub l .fam≤lub x = l .fam≤lub (f x)
      cover-preserves-is-lub l .least   ub' le = l .least ub' λ i → ∥-∥₁.proj! do
        (i' , p) ← surj i
        pure (=→≤ (ap F (sym p)) ∙ le i')

      cover-preserves-lub : Lub P F → Lub P (F ∘ₜ f)
      cover-preserves-lub l .Lub.lub = _
      cover-preserves-lub l .Lub.has-lub = cover-preserves-is-lub (l .Lub.has-lub)

      cover-reflects-is-lub : ∀ {lub} → is-lub P (F ∘ₜ f) lub → is-lub P F lub
      cover-reflects-is-lub l .fam≤lub x = ∥-∥₁.proj! do
        (y , p) ← surj x
        pure (=→≤ (ap F (sym p)) ∙ l .fam≤lub y)
      cover-reflects-is-lub l .least ub' le = l .least ub' λ i → le (f i)

      cover-reflects-lub : Lub P (F ∘ₜ f) → Lub P F
      cover-reflects-lub l .Lub.lub     = _
      cover-reflects-lub l .Lub.has-lub = cover-reflects-is-lub (l .Lub.has-lub)

  cast-is-lub
    : ∀ {ℓᵢ ℓᵢ'} {I : 𝒰 ℓᵢ} {I' : 𝒰 ℓᵢ'} {F : I → Ob} {G : I' → Ob} {lub}
    → (e : I ≃ I')
    → (∀ i → F i ＝ G (e $ i))
    → is-lub P F lub
    → is-lub P G lub
  cast-is-lub {G} e p has-lub .fam≤lub i'
    = =→≤ (sym (p (e ⁻¹ $ i') ∙ ap G (Equiv.ε e i')))
    ∙ has-lub .fam≤lub (e ⁻¹ $ i')
  cast-is-lub e p has-lub .least ub G≤ub =
    has-lub .least ub (λ i → =→≤ (p i) ∙ G≤ub (e $ i))

  cast-is-lubᶠ
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F G : I → Ob} {lub}
    → (∀ i → F i ＝ G i)
    → is-lub P F lub
    → is-lub P G lub
  cast-is-lubᶠ = cast-is-lub refl

  fam-bound→is-lub
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → (i : I) → (∀ j → F j ≤ F i)
    → is-lub P F (F i)
  fam-bound→is-lub i ge .fam≤lub = ge
  fam-bound→is-lub i ge .least y le = le i

  lub-of-const-fam
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x}
    → (∀ i j → F i ＝ F j)
    → is-lub P F x
    → ∀ i → F i ＝ x
  lub-of-const-fam {F = F} is-const x-lub i =
    ≤-antisym
      (fam≤lub x-lub i)
      (least x-lub (F i) λ j → =→≤ (sym (is-const i j)))

  const-inhabited-fam→is-lub
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x}
    → (∀ i → F i ＝ x)
    → ∥ I ∥₁
    → is-lub P F x
  const-inhabited-fam→is-lub {I} {F} {x} is-const =
    rec! mk-is-lub where
      mk-is-lub : I → is-lub P F x
      mk-is-lub i .is-lub.fam≤lub j = =→≤ (is-const j)
      mk-is-lub i .is-lub.least y le =
        x    =⟨ is-const i ⟨
        F i  ≤⟨ le i ⟩
        y    ∎

  const-inhabited-fam→lub
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → (∀ i j → F i ＝ F j)
    → ∥ I ∥₁
    → Lub P F
  const-inhabited-fam→lub {I} {F} is-const =
    rec! mk-lub where
      mk-lub : I → Lub P F
      mk-lub i .Lub.lub = F i
      mk-lub i .Lub.has-lub =
        const-inhabited-fam→is-lub (λ j → is-const j i) ∣ i ∣₁
