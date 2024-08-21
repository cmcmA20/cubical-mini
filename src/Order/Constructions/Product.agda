{-# OPTIONS --safe #-}
module Order.Constructions.Product where

open import Categories.Prelude
open import Categories.Diagram.Terminal

open import Functions.Surjection

open import Order.Base
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.SupLattice
import Order.Reasoning

private variable o ℓ o′ ℓ′ o″ ℓ″ : Level

Terminal-Poset : Terminal (Posets o ℓ)
Terminal-Poset .Terminal.top = ⊤
Terminal-Poset .Terminal.has-⊤ _ .fst .hom = _
Terminal-Poset .Terminal.has-⊤ _ .fst .pres-≤ = _
Terminal-Poset .Terminal.has-⊤ _ .snd _ = trivial!

_×ₚ_ : Poset o ℓ → Poset o′ ℓ′ → Poset (o ⊔ o′) (ℓ ⊔ ℓ′)
P ×ₚ Q = po module ×ₚ where
  module P = Order.Reasoning P
  module Q = Order.Reasoning Q

  po : Poset _ _
  po .Poset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  po .Poset._≤_ (x , x′) (y , y′) = (x ⇒ y) × (x′ ⇒ y′)
  po .Poset.≤-thin = hlevel 1
  po .Poset.≤-refl = refl , refl
  po .Poset.≤-trans (f , f′) (g , g′) = f ∙ g , f′ ∙ g′
  po .Poset.≤-antisym (p , p′) (q , q′) = ext (P.≤-antisym p q , Q.≤-antisym p′ q′)
{-# DISPLAY ×ₚ.po a b = a ×ₚ b #-}

instance
  ×-Poset : ×-notation (Poset o ℓ) (Poset o′ ℓ′) _
  ×-Poset ._×_ = _×ₚ_

module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  Fst : P × Q ⇒ P
  Fst .hom = fst
  Fst .pres-≤ = fst

  Snd : P × Q ⇒ Q
  Snd .hom = snd
  Snd .pres-≤ = snd

  Poset⟨_,_⟩ : {R : Poset o″ ℓ″} → R ⇒ P → R ⇒ Q → R ⇒ P × Q
  Poset⟨ F , G ⟩ .hom = < F .hom , G .hom >
  Poset⟨ F , G ⟩ .pres-≤ = < F .pres-≤ , G .pres-≤ >

  module _ {ℓᵢ} {I : 𝒰 ℓᵢ} {Fp : I → ⌞ P ⌟} {Fq : I → ⌞ Q ⌟} where instance
    ×-is-lub : {x : ⌞ P ⌟} {y : ⌞ Q ⌟} → ×-notation (is-lub P Fp x) (is-lub Q Fq y) (is-lub (P × Q) < Fp , Fq > (x , y))
    ×-is-lub ._×_ lp lq .is-lub.fam≤lub = < is-lub.fam≤lub lp , is-lub.fam≤lub lq >
    ×-is-lub ._×_ lp lq .is-lub.least (ubx , uby) =
      < lp .is-lub.least ubx ∘ₜ (λ a i → a i .fst) , lq .is-lub.least uby ∘ₜ (λ a i → a i .snd) >

    ×-Lub : ×-notation (Lub P Fp) (Lub Q Fq) (Lub (P × Q) < Fp , Fq >)
    ×-Lub ._×_ Lp Lq .Lub.lub = Lp .Lub.lub , Lq .Lub.lub
    ×-Lub ._×_ Lp Lq .Lub.has-lub = Lp .Lub.has-lub × Lq .Lub.has-lub

    ×-is-glb : {x : ⌞ P ⌟} {y : ⌞ Q ⌟} → ×-notation (is-glb P Fp x) (is-glb Q Fq y) (is-glb (P × Q) < Fp , Fq > (x , y))
    ×-is-glb ._×_ gp gq .is-glb.glb≤fam = < gp .is-glb.glb≤fam , gq .is-glb.glb≤fam >
    ×-is-glb ._×_ gp gq .is-glb.greatest (lbx , lby) =
      < gp .is-glb.greatest lbx ∘ₜ (λ a i → a i .fst) , gq .is-glb.greatest lby ∘ₜ (λ a i → a i .snd) >

    ×-Glb : ×-notation (Glb P Fp) (Glb Q Fq) (Glb (P × Q) < Fp , Fq >)
    ×-Glb ._×_ Gp Gq .Glb.glb     = Gp .Glb.glb , Gq .Glb.glb
    ×-Glb ._×_ Gp Gq .Glb.has-glb = Gp .Glb.has-glb × Gq .Glb.has-glb

  module _ {ℓᵢ ℓᵢ₁ ℓᵢ₂} {I : 𝒰 ℓᵢ} {I₁ : 𝒰 ℓᵢ₁} {I₂ : 𝒰 ℓᵢ₂} {Fp : I₁ → ⌞ P ⌟} {Fq : I₂ → ⌞ Q ⌟}
           (f₁ : I ↠ I₁) (f₂ : I ↠ I₂)
           where
    ×-is-lub-surj : {x : ⌞ P ⌟} {y : ⌞ Q ⌟}
                  → is-lub P Fp x
                  → is-lub Q Fq y
                  → is-lub (P × Q) {I = I} < Fp ∘ₜ f₁ #_ , Fq ∘ₜ f₂ #_ > (x , y)
    ×-is-lub-surj lp lq .is-lub.fam≤lub = < (is-lub.fam≤lub lp ∘ₜ f₁ #_) , is-lub.fam≤lub lq ∘ₜ f₂ #_ >
    ×-is-lub-surj lp lq .is-lub.least (ubx , uby) f =
        lp .is-lub.least ubx (λ i₁ → rec! (λ i e → subst (λ q → P .Poset._≤_ (Fp q) ubx) e (f i .fst)) (f₁ .snd i₁))
      , lq .is-lub.least uby (λ i₂ → rec! (λ i e → subst (λ q → Q .Poset._≤_ (Fq q) uby) e (f i .snd)) (f₂ .snd i₂))

    ×-Lub-surj : Lub P Fp
               → Lub Q Fq
               → Lub (P × Q) {I = I} < Fp ∘ₜ f₁ #_ , Fq ∘ₜ f₂ #_ >
    ×-Lub-surj Lp Lq .Lub.lub = Lp .Lub.lub , Lq .Lub.lub
    ×-Lub-surj Lp Lq .Lub.has-lub = ×-is-lub-surj (Lp .Lub.has-lub) (Lq .Lub.has-lub)

    -- TODO glb-surj

  module _ {ℓᵢ} where instance
    ×-is-sup-lattice : ×-notation (is-sup-lattice P ℓᵢ) (is-sup-lattice Q ℓᵢ) (is-sup-lattice (P ×ₚ Q) ℓᵢ)
    ×-is-sup-lattice ._×_ sx sy .is-sup-lattice.has-lubs {I} {F} =
      cast-lub refl (λ i → ×-path refl refl) $
      sx .is-sup-lattice.has-lubs {F = λ i → F i .fst} × sy .is-sup-lattice.has-lubs {F = λ i → F i .snd}
