{-# OPTIONS --safe #-}
open import Categories.Displayed.Base
open import Categories.Prelude

module Categories.Displayed.Cartesian {o ℓ o′ ℓ′}
  {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

open import Categories.Morphism B
open Displayed E

private variable
  u  : Ob
  u′ : Ob[ u ]

record is-cartesian {a b} {a′ : Ob[ a ]} {b′ : Ob[ b ]}
  (f : Hom a b) (f′ : Hom[ f ] a′ b′) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  no-eta-equality
  field
    universal : (m : Hom u a) (h′ : Hom[ f ∘ m ] u′ b′) → Hom[ m ] u′ a′
    commutes  : (m : Hom u a) (h′ : Hom[ f ∘ m ] u′ b′)
              → f′ ∘ᵈ universal m h′ ＝ h′
    unique    : {m : Hom u a} {h′ : Hom[ f ∘ m ] u′ b′}
              → (m′ : Hom[ m ] u′ a′) → f′ ∘ᵈ m′ ＝ h′ → m′ ＝ universal m h′

  universal′ : {m : Hom u a} {k : Hom u b}
             → (p : f ∘ m ＝ k) (h′ : Hom[ k ] u′ b′)
             → Hom[ m ] u′ a′
  universal′ {u′} p h′ =
    universal _ (coe1→0 (λ i → Hom[ p i ] u′ b′) h′)

  commutesᴾ : {m : Hom u a} {k : Hom u b}
            → (p : f ∘ m ＝ k) (h′ : Hom[ k ] u′ b′)
            → f′ ∘ᵈ universal′ p h′ ＝[ p ] h′
  commutesᴾ {u′} p h′ =
    to-pathᴾ⁻ $ commutes _ (coe1→0 (λ i → Hom[ p i ] u′ b′) h′)

  universalᴾ : {m₁ m₂ : Hom u a} {k : Hom u b}
             → (p : f ∘ m₁ ＝ k) (q : m₁ ＝ m₂) (r : f ∘ m₂ ＝ k)
             → (h′ : Hom[ k ] u′ b′)
             → universal′ p h′ ＝[ q ] universal′ r h′
  universalᴾ {u} p q r h′ i =
    universal′ (is-set→squareᴾ (λ _ _ → Hom-set u b) (ap (f ∘_) q) p r refl i) h′

  uniqueᴾ : {m₁ m₂ : Hom u a} {k : Hom u b}
          → (p : f ∘ m₁ ＝ k) (q : m₁ ＝ m₂) (r : f ∘ m₂ ＝ k)
          → {h′ : Hom[ k ] u′ b′}
          → (m′ : Hom[ m₁ ] u′ a′)
          → f′ ∘ᵈ m′ ＝[ p ] h′ → m′ ＝[ q ] universal′ r h′
  uniqueᴾ p q r {h′} m′ s =
    to-pathᴾ⁻ (unique m′ (from-pathᴾ⁻ s) ∙ from-pathᴾ⁻ (universalᴾ p q r h′))

  uniqueᴾ²
    : {m₁ m₂ : Hom u a} {k : Hom u b}
    → (p : f ∘ m₁ ＝ k) (q : m₁ ＝ m₂) (r : f ∘ m₂ ＝ k)
    → {h′ : Hom[ k ] u′ b′} (m₁′ : Hom[ m₁ ] u′ a′) (m₂′ : Hom[ m₂ ] u′ a′)
    → f′ ∘ᵈ m₁′ ＝[ p ] h′
    → f′ ∘ᵈ m₂′ ＝[ r ] h′
    → m₁′ ＝[ q ] m₂′
  uniqueᴾ² {u′} p q r m₁′ m₂′ α β = to-pathᴾ⁻ $
       unique m₁′ (from-pathᴾ⁻ α)
    ∙∙ from-pathᴾ⁻ (universalᴾ p q r _)
    ∙∙ ap (coe1→0 (λ i → Hom[ q i ] u′ a′)) (sym (unique m₂′ (from-pathᴾ⁻ β)))

  universalⱽ : ∀ {a″} (f″ : Hom[ f ] a″ b′) → Hom[ id ] a″ a′
  universalⱽ f″ = universal′ (id-r _) f″

  commutesⱽ
    : ∀ {x′} (g′ : Hom[ f ] x′ b′)
    → f′ ∘ᵈ universalⱽ g′ ＝[ id-r _ ] g′
  commutesⱽ = commutesᴾ (id-r _)

  uniqueⱽ
    : ∀ {x′} {g′ : Hom[ f ] x′ b′}
    → (h′ : Hom[ id ] x′ a′)
    → f′ ∘ᵈ h′ ＝[ id-r _ ] g′
    → h′ ＝ universalⱽ g′
  uniqueⱽ h′ p = uniqueᴾ (id-r f) refl (id-r f) h′ p

  uniqueⱽ²
    : ∀ {x′} {g′ : Hom[ f ] x′ b′}
    → (h′ h″ : Hom[ id ] x′ a′)
    → f′ ∘ᵈ h′ ＝[ id-r _ ] g′
    → f′ ∘ᵈ h″ ＝[ id-r _ ] g′
    → h′ ＝ h″
  uniqueⱽ² h′ h″ p q =
    uniqueᴾ² (id-r f) refl (id-r f) h′ h″ p q

unquoteDecl is-cartesian-iso = declare-record-iso is-cartesian-iso (quote is-cartesian)

opaque
  is-cartesian-is-prop
    : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
    → is-prop (is-cartesian f f′)
  is-cartesian-is-prop a b = Equiv.injective (≅ₜ→≃ is-cartesian-iso)
    $   ext (λ m h′ → b .unique (a .universal m h′) (a .commutes m h′))
    ,ₚ prop! where open is-cartesian

instance
  H-Level-is-cartesian : ∀ {n} {a b} {f : Hom a b} {a′ b′} {f′ : Hom[ f ] a′ b′}
                       → H-Level (suc n) (is-cartesian f f′)
  H-Level-is-cartesian = hlevel-basic-instance 1 is-cartesian-is-prop


record Cartesian-morphism
  {x y : Ob} (f : Hom x y) (x′ : Ob[ x ]) (y′ : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      hom′ : Hom[ f ] x′ y′
      cartesian : is-cartesian f hom′

instance
  unquoteDecl H-Level-cartesian-morphism =
    declare-record-hlevel 2 H-Level-cartesian-morphism (quote Cartesian-morphism)

Cartesian-morphism-pathᴾ
  : ∀ {x y x′ y′} {f g : Hom x y}
  → {f′ : Cartesian-morphism f x′ y′} {g′ : Cartesian-morphism g x′ y′}
  → {p : f ＝ g}
  → ＜ Cartesian-morphism.hom′ f′ ／ (λ i → Hom[ p i ] x′ y′) ＼ Cartesian-morphism.hom′ g′ ＞
  → ＜ f′ ／ (λ i → Cartesian-morphism (p i) x′ y′) ＼ g′ ＞
Cartesian-morphism-pathᴾ q i .Cartesian-morphism.hom′ = q i
Cartesian-morphism-pathᴾ {f′ = f′} {g′ = g′} {p = p} q i .Cartesian-morphism.cartesian =
  is-prop→pathᴾ (λ i → is-cartesian-is-prop {f = p i} {f′ = q i})
    (Cartesian-morphism.cartesian f′)
    (Cartesian-morphism.cartesian g′) i

-- TODO theorems about cartesian stuff
