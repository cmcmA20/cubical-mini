{-# OPTIONS --safe #-}
module Order.SupLattice where

open import Categories.Prelude
open import Meta.Prelude

open import Functions.Surjection

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

-- TODO move to Order.Diagram.Lub
reindexing-along-surj-＝-sup : {ℓ″ ℓ‴ : Level} {T : 𝒰 ℓ″} {T′ : 𝒰 ℓ‴}
                               {P : Poset o ℓ}
                             → (e : T′ ↠ T)
                             → (m : T → ⌞ P ⌟)
                             → (s s' : ⌞ P ⌟)
                             → is-lub P m s
                             → is-lub P (m ∘ e .fst) s'
                             → s ＝ s'
reindexing-along-surj-＝-sup {P} e m s s' l1 l2 =
  let open Poset P in
  ≤-antisym
    (is-lub.least l1 s' λ t → ∥-∥₁.elim {P = λ _ → m t ≤ s'}
                                        (λ _ → ≤-thin)
                                        (λ x → subst (λ q → m q ≤ s') (x .snd) (is-lub.fam≤lub l2 (x .fst)))
                                        (e .snd t))
    (is-lub.least l2 s λ t′ → is-lub.fam≤lub l1 (e .fst t′))

reindexing-along-equiv-＝-sup : {ℓ″ ℓ‴ : Level} {T : 𝒰 ℓ″} {T′ : 𝒰 ℓ‴}
                                {P : Poset o ℓ}
                              → (e : T′ ≃ T)
                              → (m : T → ⌞ P ⌟)
                              → (s s' : ⌞ P ⌟)
                              → is-lub P m s
                              → is-lub P (m ∘ e .fst) s'
                              → s ＝ s'
reindexing-along-equiv-＝-sup = reindexing-along-surj-＝-sup ∘ ≃→↠
