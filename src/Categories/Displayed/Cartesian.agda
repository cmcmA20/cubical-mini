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

  commutesP : {m : Hom u a} {k : Hom u b}
            → (p : f ∘ m ＝ k) (h′ : Hom[ k ] u′ b′)
            → f′ ∘ᵈ universal′ p h′ ＝[ p ] h′
  commutesP {u′} p h′ =
    to-pathP⁻ $ commutes _ (coe1→0 (λ i → Hom[ p i ] u′ b′) h′)

  universalP : {m₁ m₂ : Hom u a} {k : Hom u b}
             → (p : f ∘ m₁ ＝ k) (q : m₁ ＝ m₂) (r : f ∘ m₂ ＝ k)
             → (h′ : Hom[ k ] u′ b′)
             → universal′ p h′ ＝[ q ] universal′ r h′
  universalP {u} p q r h′ i =
    universal′ (is-set→squareP (λ _ _ → Hom-set u b) (ap (f ∘_) q) p r refl i) h′

  uniqueP : {m₁ m₂ : Hom u a} {k : Hom u b}
          → (p : f ∘ m₁ ＝ k) (q : m₁ ＝ m₂) (r : f ∘ m₂ ＝ k)
          → {h′ : Hom[ k ] u′ b′}
          → (m′ : Hom[ m₁ ] u′ a′)
          → f′ ∘ᵈ m′ ＝[ p ] h′ → m′ ＝[ q ] universal′ r h′
  uniqueP p q r {h′} m′ s =
    to-pathP⁻ (unique m′ (from-pathP⁻ s) ∙ from-pathP⁻ (universalP p q r h′))

  uniqueP²
    : {m₁ m₂ : Hom u a} {k : Hom u b}
    → (p : f ∘ m₁ ＝ k) (q : m₁ ＝ m₂) (r : f ∘ m₂ ＝ k)
    → {h′ : Hom[ k ] u′ b′} (m₁′ : Hom[ m₁ ] u′ a′) (m₂′ : Hom[ m₂ ] u′ a′)
    → f′ ∘ᵈ m₁′ ＝[ p ] h′
    → f′ ∘ᵈ m₂′ ＝[ r ] h′
    → m₁′ ＝[ q ] m₂′
  uniqueP² {u′} p q r m₁′ m₂′ α β = to-pathP⁻ $
       unique m₁′ (from-pathP⁻ α)
    ∙∙ from-pathP⁻ (universalP p q r _)
    ∙∙ ap (coe1→0 (λ i → Hom[ q i ] u′ a′)) (sym (unique m₂′ (from-pathP⁻ β)))

  universalV : ∀ {a″} (f″ : Hom[ f ] a″ b′) → Hom[ id ] a″ a′
  universalV f″ = universal′ (id-r _) f″

  commutesV
    : ∀ {x′} (g′ : Hom[ f ] x′ b′)
    → f′ ∘ᵈ universalV g′ ＝[ id-r _ ] g′
  commutesV = commutesP (id-r _)

  uniqueV
    : ∀ {x′} {g′ : Hom[ f ] x′ b′}
    → (h′ : Hom[ id ] x′ a′)
    → f′ ∘ᵈ h′ ＝[ id-r _ ] g′
    → h′ ＝ universalV g′
  uniqueV h′ p = uniqueP (id-r f) refl (id-r f) h′ p

  uniqueV²
    : ∀ {x′} {g′ : Hom[ f ] x′ b′}
    → (h′ h″ : Hom[ id ] x′ a′)
    → f′ ∘ᵈ h′ ＝[ id-r _ ] g′
    → f′ ∘ᵈ h″ ＝[ id-r _ ] g′
    → h′ ＝ h″
  uniqueV² h′ h″ p q =
    uniqueP² (id-r f) refl (id-r f) h′ h″ p q


opaque
  unfolding is-of-hlevel
  is-cartesian-is-prop
    : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
    → is-prop (is-cartesian f f′)
  is-cartesian-is-prop {f′} cart cart′ = worker where
    open is-cartesian
    worker : cart ＝ cart′
    worker i .universal m h′ =
      cart′ .unique (cart .universal m h′) (cart .commutes _ _) i
    worker i .commutes m h′ =
      is-set→squareP (λ _ _ → Hom[ _ ]-set _ _)
        (ap (f′ ∘ᵈ_) (cart′ .unique _ _))
        (cart .commutes m h′)
        (cart′ .commutes m h′)
        refl i
    worker i .unique m′ p =
      is-set→squareP (λ _ _ → Hom[ _ ]-set _ _)
        refl
        (cart .unique m′ p)
        (cart′ .unique m′ p)
        (cart′ .unique _ _) i

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

unquoteDecl cartesian-morphism-iso = declare-record-iso cartesian-morphism-iso (quote Cartesian-morphism)

Cartesian-morphism-pathP
  : ∀ {x y x′ y′} {f g : Hom x y}
  → {f′ : Cartesian-morphism f x′ y′} {g′ : Cartesian-morphism g x′ y′}
  → {p : f ＝ g}
  → ＜ Cartesian-morphism.hom′ f′ ／ (λ i → Hom[ p i ] x′ y′) ＼ Cartesian-morphism.hom′ g′ ＞
  → ＜ f′ ／ (λ i → Cartesian-morphism (p i) x′ y′) ＼ g′ ＞
Cartesian-morphism-pathP q i .Cartesian-morphism.hom′ = q i
Cartesian-morphism-pathP {f′ = f′} {g′ = g′} {p = p} q i .Cartesian-morphism.cartesian =
  is-prop→pathP (λ i → is-cartesian-is-prop {f = p i} {f′ = q i})
    (Cartesian-morphism.cartesian f′)
    (Cartesian-morphism.cartesian g′) i

Cartesian-morphism-is-set
  : ∀ {x y x′ y′} {f : Hom x y}
  → is-set (Cartesian-morphism f x′ y′)
Cartesian-morphism-is-set = iso→is-of-hlevel 2 cartesian-morphism-iso hlevel!

-- TODO theorems about cartesian stuff
