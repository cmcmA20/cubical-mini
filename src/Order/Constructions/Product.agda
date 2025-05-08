{-# OPTIONS --safe #-}
module Order.Constructions.Product where

open import Cat.Prelude
open import Cat.Diagram.Terminal

open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Top
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Strict
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Lattice

open import Functions.Surjection

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
  po .Poset._≤_ (x , x′) (y , y′) = (x P.≤ y) × (x′ Q.≤ y′)
  po .Poset.≤-thin = hlevel 1
  po .Poset.≤-refl = refl , refl
  po .Poset.≤-trans (f , f′) (g , g′) = f ∙ g , f′ ∙ g′
  po .Poset.≤-antisym (p , p′) (q , q′) = ext (P.≤-antisym p q , Q.≤-antisym p′ q′)
{-# DISPLAY ×ₚ.po a b = a ×ₚ b #-}

instance
  ×-Poset : ×-notation (Poset o ℓ) (Poset o′ ℓ′) _
  ×-Poset .×-notation.Constraint _ _ = ⊤
  ×-Poset ._×_ P Q = P ×ₚ Q

_×ₛ_ : StrictPoset o ℓ → StrictPoset o′ ℓ′ → StrictPoset (o ⊔ o′) (ℓ ⊔ ℓ′)
P ×ₛ Q = spo module ×ₛ where
  module P = StrictPoset P
  module Q = StrictPoset Q

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  spo .StrictPoset._<_ (x , x′) (y , y′) = (x P.< y) × (x′ Q.< y′)
  spo .StrictPoset.<-thin = hlevel 1
  spo .StrictPoset.<-irrefl (p′ , _) = P.<-irrefl p′
  spo .StrictPoset.<-trans (p , p′) (q , q′) = p ∙ q , p′ ∙ q′
{-# DISPLAY ×ₛ.spo a b = a ×ₛ b #-}

instance
  ×-StrictPoset : ×-notation (StrictPoset o ℓ) (StrictPoset o′ ℓ′) _
  ×-StrictPoset .×-notation.Constraint _ _ = ⊤
  ×-StrictPoset ._×_ P Q = P ×ₛ Q

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

  module _ {a : ⌞ P ⌟} {x : ⌞ Q ⌟} where

    ×-is-bottom : ×-notation (is-bottom P a) (is-bottom Q x) (is-bottom (P × Q) (a , x))
    ×-is-bottom .×-notation.Constraint _ _ = ⊤
    ×-is-bottom .×-notation._×_ α β (p , q) = α p , β q

    ×-is-top : ×-notation (is-top P a) (is-top Q x) (is-top (P × Q) (a , x))
    ×-is-top .×-notation.Constraint _ _ = ⊤
    ×-is-top .×-notation._×_ α β (p , q) = α p , β q

    module _ {b : ⌞ P ⌟} {y : ⌞ Q ⌟} where

      module _ {c : ⌞ P ⌟} {z : ⌞ Q ⌟ } where instance
        ×-is-join : ×-notation (is-join P a b c) (is-join Q x y z) (is-join (P × Q) (a , x) (b , y) (c , z))
        ×-is-join .×-notation.Constraint _ _ = ⊤
        ×-is-join ._×_ lp lq .is-join.l≤join = lp .is-join.l≤join , lq .is-join.l≤join
        ×-is-join ._×_ lp lq .is-join.r≤join = lp .is-join.r≤join , lq .is-join.r≤join
        ×-is-join ._×_ lp lq .is-join.least (ub₁ , ub₂) (al , xl) (bl , yl) =
          lp .is-join.least ub₁ al bl , lq .is-join.least ub₂ xl yl

        ×-is-meet : ×-notation (is-meet P a b c) (is-meet Q x y z) (is-meet (P × Q) (a , x) (b , y) (c , z))
        ×-is-meet .×-notation.Constraint _ _ = ⊤
        ×-is-meet ._×_ lp lq .is-meet.meet≤l = lp .is-meet.meet≤l , lq .is-meet.meet≤l
        ×-is-meet ._×_ lp lq .is-meet.meet≤r = lp .is-meet.meet≤r , lq .is-meet.meet≤r
        ×-is-meet ._×_ lp lq .is-meet.greatest (ub₁ , ub₂) (al , xl) (bl , yl) =
          lp .is-meet.greatest ub₁ al bl , lq .is-meet.greatest ub₂ xl yl

      instance
        ×-Join : ×-notation (Join P a b) (Join Q x y) (Join (P × Q) (a , x) (b , y))
        ×-Join .×-notation.Constraint _ _ = ⊤
        ×-Join ._×_ α β .Join.lub      = α .Join.lub , β .Join.lub
        ×-Join ._×_ α β .Join.has-join = α .Join.has-join × β .Join.has-join

        ×-Meet : ×-notation (Meet P a b) (Meet Q x y) (Meet (P × Q) (a , x) (b , y))
        ×-Meet .×-notation.Constraint _ _ = ⊤
        ×-Meet ._×_ α β .Meet.glb      = α .Meet.glb , β .Meet.glb
        ×-Meet ._×_ α β .Meet.has-meet = α .Meet.has-meet × β .Meet.has-meet

  instance
    ×-Bottom : ×-notation (Bottom P) (Bottom Q) (Bottom (P × Q))
    ×-Bottom .×-notation.Constraint _ _ = ⊤
    ×-Bottom ._×_ α β .Bottom.bot = α .Bottom.bot , β .Bottom.bot
    ×-Bottom ._×_ α β .Bottom.bot-is-bot = α .Bottom.bot-is-bot × β .Bottom.bot-is-bot

    ×-Top : ×-notation (Top P) (Top Q) (Top (P × Q))
    ×-Top .×-notation.Constraint _ _ = ⊤
    ×-Top ._×_ α β .Top.top = α .Top.top , β .Top.top
    ×-Top ._×_ α β .Top.top-is-top = α .Top.top-is-top × β .Top.top-is-top

    ×-is-join-semilattice : ×-notation (is-join-semilattice P) (is-join-semilattice Q) (is-join-semilattice (P × Q))
    ×-is-join-semilattice .×-notation.Constraint _ _ = ⊤
    ×-is-join-semilattice .×-notation._×_ α β .is-join-semilattice.has-bottom =
      α .is-join-semilattice.has-bottom × β .is-join-semilattice.has-bottom
    ×-is-join-semilattice .×-notation._×_ α β .is-join-semilattice.has-joins =
      α .is-join-semilattice.has-joins × β .is-join-semilattice.has-joins

    ×-is-meet-semilattice : ×-notation (is-meet-semilattice P) (is-meet-semilattice Q) (is-meet-semilattice (P × Q))
    ×-is-meet-semilattice .×-notation.Constraint _ _ = ⊤
    ×-is-meet-semilattice .×-notation._×_ α β .is-meet-semilattice.has-top =
      α .is-meet-semilattice.has-top × β .is-meet-semilattice.has-top
    ×-is-meet-semilattice .×-notation._×_ α β .is-meet-semilattice.has-meets =
      α .is-meet-semilattice.has-meets × β .is-meet-semilattice.has-meets

    ×-is-lattice : ×-notation (is-lattice P) (is-lattice Q) (is-lattice (P × Q))
    ×-is-lattice .×-notation.Constraint _ _ = ⊤
    ×-is-lattice .×-notation._×_ α β .is-lattice.has-join-slat =
      α .is-lattice.has-join-slat × β .is-lattice.has-join-slat
    ×-is-lattice .×-notation._×_ α β .is-lattice.has-meet-slat =
      α .is-lattice.has-meet-slat × β .is-lattice.has-meet-slat

  module _ {I : 𝒰 ℓᵢ} {F : I → ⌞ P ⌟} {G : I → ⌞ Q ⌟} where
    module _ {x : ⌞ P ⌟} {y : ⌞ Q ⌟} where instance
      ×-is-lub : ×-notation (is-lub P F x) (is-lub Q G y) (is-lub (P × Q) < F , G > (x , y))
      ×-is-lub .×-notation.Constraint _ _ = ⊤
      ×-is-lub ._×_ lp lq .is-lub.fam≤lub = < is-lub.fam≤lub lp , is-lub.fam≤lub lq >
      ×-is-lub ._×_ lp lq .is-lub.least (ubx , uby) =
        < (λ a i → a i .fst) ∙ lp .is-lub.least ubx , (λ a i → a i .snd) ∙ lq .is-lub.least uby >

      ×-is-glb : ×-notation (is-glb P F x) (is-glb Q G y) (is-glb (P × Q) < F , G > (x , y))
      ×-is-glb .×-notation.Constraint _ _ = ⊤
      ×-is-glb ._×_ gp gq .is-glb.glb≤fam = < gp .is-glb.glb≤fam , gq .is-glb.glb≤fam >
      ×-is-glb ._×_ gp gq .is-glb.greatest (lbx , lby) =
        < (λ a i → a i .fst) ∙ gp .is-glb.greatest lbx , (λ a i → a i .snd) ∙ gq .is-glb.greatest lby >

    instance
      ×-Lub : ×-notation (Lub P F) (Lub Q G) (Lub (P × Q) < F , G >)
      ×-Lub .×-notation.Constraint _ _ = ⊤
      ×-Lub ._×_ Lp Lq .Lub.lub = Lp .Lub.lub , Lq .Lub.lub
      ×-Lub ._×_ Lp Lq .Lub.has-lub = Lp .Lub.has-lub × Lq .Lub.has-lub

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
