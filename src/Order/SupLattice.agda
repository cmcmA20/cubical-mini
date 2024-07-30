{-# OPTIONS --safe #-}
module Order.SupLattice where

open import Categories.Prelude
open import Meta.Prelude
open import Foundations.Equiv.Size

open import Functions.Surjection
open import Combinatorics.Power

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
import Order.Reasoning

private variable
  o ℓ ℓ′ : Level

record is-sup-lattice (P : Poset o ℓ) (ℓ′ : Level) : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  open Poset P

  field
    sup : ∀ {I : 𝒰 ℓ′} → (I → Ob) → Ob
    suprema : {I : 𝒰 ℓ′} (F : I → Ob) → is-lub P F (sup F)


module _ {o ℓ ℓ′ : Level}
         {P : Poset o ℓ}
         (L : is-sup-lattice P ℓ′)
         {T : 𝒰 ℓ′}
         (m : T → ⌞ P ⌟)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L

  joins-preserve-containment : {P Q : ℙ T ℓ′}
                             → P ⊆ Q
                             → sup (ℙ→fam m P .snd) ≤ sup (ℙ→fam m Q .snd)
  joins-preserve-containment {P} {Q} C =
    suprema (ℙ→fam m P .snd) .least (sup (ℙ→fam m Q .snd)) $
    suprema (ℙ→fam m Q .snd) .fam≤lub ∘ second C

module _ {o ℓ ℓ′ ℓ″ : Level}
         {P : Poset o ℓ}
         (L : is-sup-lattice P ℓ′)
         {T : 𝒰 ℓ″}
         (m : T → ⌞ P ⌟)
         (T-sz : has-size ℓ′ T)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L

  private
    T' : 𝒰 ℓ′
    T' = resized T-sz

    T'≃T : T' ≃ T
    T'≃T = resizing-cond T-sz

    T'→T : T' → T
    T'→T = T'≃T $_

    T'-inclusion : T' → Ob
    T'-inclusion = m ∘ T'→T

  sup-of-small-fam-is-lub : is-lub P m (sup T'-inclusion)
  sup-of-small-fam-is-lub .fam≤lub t = subst (λ q → m q ≤ sup T'-inclusion)
                                             (is-equiv→unit ((T'≃T ⁻¹) .snd) t)
                                             (suprema T'-inclusion .fam≤lub (T'≃T ⁻¹ $ t))
  sup-of-small-fam-is-lub .least u' ub = suprema T'-inclusion .least u' (ub ∘ T'→T)


-- TODO move to Order.Diagram.Lub ?

module _ {o ℓ ℓ′ ℓ″ : Level}
         {T : 𝒰 ℓ′} {T′ : 𝒰 ℓ″}
         {P : Poset o ℓ}
         (e : T′ ↠ T)
         (m : T → ⌞ P ⌟)
       where

  open Poset P
  open is-lub

  reindexing-along-surj-=-sup : (s s' : Ob)
                               → is-lub P m s
                               → is-lub P (m ∘ (e $_)) s'
                               → s ＝ s'
  reindexing-along-surj-=-sup s s' l1 l2 =
    ≤-antisym
      (least l1 s' λ t → ∥-∥₁.elim (λ _ → ≤-thin)
                                          (λ x → subst (λ q → m q ≤ s') (x .snd) (fam≤lub l2 (x .fst)))
                                          (e .snd t))
      (least l2 s λ t′ → fam≤lub l1 (e $ t′))

module _ {o ℓ ℓ′ ℓ″ : Level}
         {T : 𝒰 ℓ′} {T′ : 𝒰 ℓ″}
         {P : Poset o ℓ}
         (e : T′ ≃ T)
         (m : T → ⌞ P ⌟)
       where

  open Poset P

  reindexing-along-equiv-=-sup : (s s' : Ob)
                                → is-lub P m s
                                → is-lub P (m ∘ (e $_)) s'
                                → s ＝ s'
  reindexing-along-equiv-=-sup = reindexing-along-surj-=-sup (≃→↠ e) m
