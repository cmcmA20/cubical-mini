{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Glb

module Order.Diagram.Glb.Reasoning
  {o ℓ} (P : Poset o ℓ) {ℓ′} (hl : Has-glbs-of-size P ℓ′)
  where

open import Algebra.Monoid.Commutative
open import Cat.Prelude

open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Reasoning P

open import Data.Bool as Bool

glbs : {I : Type ℓ′} (F : I → Ob) → Glb P F
glbs F = hl {F = F}

⋂ : {I : Type ℓ′} (F : I → Ob) → Ob
⋂ F = glbs F .Glb.glb

module glbs {I} {F} = Glb (glbs {I} F)
open glbs renaming
  ( glb≤fam  to ⋂-proj
  ; greatest to ⋂-universal
  ) public

Top-Poset-Lub : Top P
Top-Poset-Lub .Top.top = ⋂ {I = Lift ℓ′ ⊥} λ()
Top-Poset-Lub .Top.has-top _ = ⋂-universal _ λ ()

Meet-Poset-Glb : Has-meets P
Meet-Poset-Glb {x} {y} .Meet.glb = ⋂ {I = Lift ℓ′ Bool} (rec! (if_then x else y))
Meet-Poset-Glb .Meet.has-meet .is-meet.meet≤l = ⋂-proj (lift true)
Meet-Poset-Glb .Meet.has-meet .is-meet.meet≤r = ⋂-proj (lift false)
Meet-Poset-Glb .Meet.has-meet .is-meet.greatest ub′ p q = ⋂-universal _ (elim! (Bool.elim p q))

open Top Top-Poset-Lub public
open import Order.Diagram.Meet.Reasoning P Meet-Poset-Glb public

⋂≤⋂-over
  : {I J : Type ℓ′} {f : J → Ob} {g : I → Ob}
  → (to : I → J)
  → (∀ i → f (to i) ≤ g i)
  → ⋂ f ≤ ⋂ g
⋂≤⋂-over to p = ⋂-universal _ λ i → ⋂-proj (to i) ∙ p i

⋂≤⋂
  : {I : Type ℓ′} {f g : I → Ob}
  → (∀ i → f i ≤ g i)
  → ⋂ f ≤ ⋂ g
⋂≤⋂ = ⋂≤⋂-over refl

opaque
  ⋂-twice
    : {I : Type ℓ′} {J : I → Type ℓ′} (F : (i : I) → J i → Ob)
    →  ⋂ (λ i → ⋂ λ j → F i j)
    ＝ ⋂ {I = Σ[ i ꞉ I ] J i} (λ p → F (p .fst) (p .snd))
  ⋂-twice F = ≤-antisym
    (⋂-universal _ (λ (i , j) → ⋂-proj i ∙ ⋂-proj j))
    (⋂-universal _ λ i → ⋂-universal _ λ j → ⋂-proj (i , j))

  ⋂-singleton
    : {I : Type ℓ′} {f : I → Ob}
    → (p : is-contr I)
    → ⋂ f ＝ f (centre p)
  ⋂-singleton {f} p = ≤-antisym
    (⋂-proj _)
    (⋂-universal _ (λ i → =→≤ (ap f (paths p i))))

module @0 _ {I : Type ℓ′} where opaque
  ⋂-ap
    : {I′ : Type ℓ′} {f : I → Ob} {g : I′ → Ob}
    → (e : I ≃ I′)
    → (∀ i → f i ＝ g (e $ i))
    → ⋂ f ＝ ⋂ g
  ⋂-ap e p = ap² (λ _ → ⋂) (ua e) (ua→ p)

  -- raised i for "index", raised f for "family"
  ⋂-apⁱ : {I′ : Type ℓ′} {f : I′ → Ob} (e : I ≃ I′) → ⋂ {I = I} (λ i → f (e # i)) ＝ ⋂ f
  ⋂-apⁱ e = ⋂-ap e (λ _ → refl)

  ⋂-apᶠ : {f g : I → Ob} → (∀ i → f i ＝ g i) → ⋂ f ＝ ⋂ g
  ⋂-apᶠ p = ⋂-ap refl p

∩-distrib-⋂-≤l
  : {I : Type ℓ′} {x : Ob} {f : I → Ob}
  → x ∩ ⋂ f ≤ ⋂ λ i → x ∩ f i
∩-distrib-⋂-≤l =
  (⋂-universal _ λ i → ∩-universal _ ∩≤l (∩≤r ∙ ⋂-proj i))

∩-distrib-nonempty-⋂-l
  : {I : Type ℓ′} {x : Ob} {f : I → Ob}
  → ∥ I ∥₁
  → x ∩ ⋂ f ＝ ⋂ (λ i → x ∩ f i)
∩-distrib-nonempty-⋂-l i =
  ≤-antisym
   ∩-distrib-⋂-≤l
   (rec! (λ i → ∩-universal _ (⋂-proj i ∙ ∩≤l) (⋂≤⋂ λ _ → ∩≤r)) i)

opaque
  ∩-id-l : {x : Ob} → ⊤ ∩ x ＝ x
  ∩-id-l {x} = ≤-antisym
    ∩≤r
    (∩-universal _ ! refl)

  ∩-id-r : {x : Ob} → x ∩ ⊤ ＝ x
  ∩-id-r {x} = ≤-antisym
    ∩≤l
    (∩-universal _ refl !)

  ∩-is-comm-monoid : is-comm-monoid {A = Ob} _∩_
  ∩-is-comm-monoid = to-is-comm-monoid go where
    open make-comm-monoid
    go : make-comm-monoid Ob
    go .monoid-is-set = ob-is-set
    go .id = ⊤
    go ._⋆_ = _∩_
    go .id-l _ = ∩-id-l
    go .id-r _ = ∩-id-r
    go .assoc _ _ _ = ∩-assoc
    go .comm _ _ = ∩-comm
