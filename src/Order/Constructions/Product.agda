{-# OPTIONS --safe #-}
module Order.Constructions.Product where

open import Cat.Prelude
open import Cat.Diagram.Terminal

open import Functions.Surjection

open import Order.Base
open import Order.Diagram.Glb
open import Order.Diagram.Lub

private variable o ℓ o′ ℓ′ o″ ℓ″ ℓᵢ ℓⱼ ℓₖ : Level

Terminal-Poset : Terminal (Posets o ℓ)
Terminal-Poset .Terminal.top = ⊤
Terminal-Poset .Terminal.has-⊤ _ .fst .hom = _
Terminal-Poset .Terminal.has-⊤ _ .fst .pres-≤ = _
Terminal-Poset .Terminal.has-⊤ _ .snd _ = trivial!

_×ₚ_ : Poset o ℓ → Poset o′ ℓ′ → Poset (o ⊔ o′) (ℓ ⊔ ℓ′)
P ×ₚ Q = po module ×ₚ where
  module P = Poset P
  module Q = Poset Q

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
  ×-Poset .×-notation.Constraint _ _ = ⊤
  ×-Poset ._×_ P Q = P ×ₚ Q

module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  private
    module P = Poset P
    module Q = Poset Q

  Fst : P × Q ⇒ P
  Fst .hom = fst
  Fst .pres-≤ = fst

  Snd : P × Q ⇒ Q
  Snd .hom = snd
  Snd .pres-≤ = snd

  Poset⟨_,_⟩ : {R : Poset o″ ℓ″} → R ⇒ P → R ⇒ Q → R ⇒ P × Q
  Poset⟨ F , G ⟩ .hom = < F .hom , G .hom >
  Poset⟨ F , G ⟩ .pres-≤ = < F .pres-≤ , G .pres-≤ >

  module _ {I : 𝒰 ℓᵢ} {F : I → ⌞ P ⌟} {G : I → ⌞ Q ⌟} where instance
    ×-is-lub : {x : ⌞ P ⌟} {y : ⌞ Q ⌟} → ×-notation (is-lub P F x) (is-lub Q G y) (is-lub (P × Q) < F , G > (x , y))
    ×-is-lub .×-notation.Constraint _ _ = ⊤
    ×-is-lub ._×_ lp lq .is-lub.fam≤lub = < is-lub.fam≤lub lp , is-lub.fam≤lub lq >
    ×-is-lub ._×_ lp lq .is-lub.least (ubx , uby) =
      < (λ a i → a i .fst) ∙ lp .is-lub.least ubx , (λ a i → a i .snd) ∙ lq .is-lub.least uby >

    ×-Lub : ×-notation (Lub P F) (Lub Q G) (Lub (P × Q) < F , G >)
    ×-Lub .×-notation.Constraint _ _ = ⊤
    ×-Lub ._×_ Lp Lq .Lub.lub = Lp .Lub.lub , Lq .Lub.lub
    ×-Lub ._×_ Lp Lq .Lub.has-lub = Lp .Lub.has-lub × Lq .Lub.has-lub

    ×-is-glb : {x : ⌞ P ⌟} {y : ⌞ Q ⌟} → ×-notation (is-glb P F x) (is-glb Q G y) (is-glb (P × Q) < F , G > (x , y))
    ×-is-glb .×-notation.Constraint _ _ = ⊤
    ×-is-glb ._×_ gp gq .is-glb.glb≤fam = < gp .is-glb.glb≤fam , gq .is-glb.glb≤fam >
    ×-is-glb ._×_ gp gq .is-glb.greatest (lbx , lby) =
      < (λ a i → a i .fst) ∙ gp .is-glb.greatest lbx , (λ a i → a i .snd) ∙ gq .is-glb.greatest lby >

    ×-Glb : ×-notation (Glb P F) (Glb Q G) (Glb (P × Q) < F , G >)
    ×-Glb .×-notation.Constraint _ _ = ⊤
    ×-Glb ._×_ Gp Gq .Glb.glb     = Gp .Glb.glb , Gq .Glb.glb
    ×-Glb ._×_ Gp Gq .Glb.has-glb = Gp .Glb.has-glb × Gq .Glb.has-glb

  module _ {I : 𝒰 ℓᵢ} {J : 𝒰 ℓⱼ} {K : 𝒰 ℓₖ} {F : J → ⌞ P ⌟} {G : K → ⌞ Q ⌟}
           (f₁ : I ↠ J) (f₂ : I ↠ K)
           where
    ×-is-lub-surj : {x : ⌞ P ⌟} {y : ⌞ Q ⌟}
                  → is-lub P F x
                  → is-lub Q G y
                  → is-lub (P × Q) < f₁ #_ ∙ F , f₂ #_ ∙ G > (x , y)
    ×-is-lub-surj lp lq .is-lub.fam≤lub = < lp .is-lub.fam≤lub ∘ₜ f₁ #_ , lq .is-lub.fam≤lub ∘ₜ f₂ #_ >
    ×-is-lub-surj lp lq .is-lub.least (ubx , uby) f =
        lp .is-lub.least ubx (λ j → case f₁ .snd j of λ j₁ e → =→~⁻ (F # e) ∙ f j₁ .fst)
      , lq .is-lub.least uby (λ k → case f₂ .snd k of λ k₁ e → =→~⁻ (G # e) ∙ f k₁ .snd)

    ×-Lub-surj : Lub P F
               → Lub Q G
               → Lub (P × Q) < f₁ #_ ∙ F , f₂ #_ ∙ G >
    ×-Lub-surj Lp Lq .Lub.lub = Lp .Lub.lub , Lq .Lub.lub
    ×-Lub-surj Lp Lq .Lub.has-lub = ×-is-lub-surj (Lp .Lub.has-lub) (Lq .Lub.has-lub)

    -- TODO glb-surj
