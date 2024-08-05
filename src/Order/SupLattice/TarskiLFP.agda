{-# OPTIONS --safe #-}
module Order.SupLattice.TarskiLFP where

open import Categories.Prelude

open import Data.Empty
open import Data.Unit

open import Combinatorics.Power
open import Functions.Surjection

open import Order.Diagram.Fixpoint
open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice
open import Order.SupLattice.SmallBasis
import Order.SupLattice.SmallPresentation as small-presentation-of-lattice
import Order.Reasoning

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
        where
  open Order.Reasoning P
  open is-sup-lattice L
  open is-basis h

  c-closure : {ℓ″ : Level} (S : ℙ B ℓ″) → 𝒰 (ℓsuc ℓ′ ⊔ ℓ″)
  c-closure S = (U : ℙ B ℓ′) → U ⊆ S → (b : B) → b ≤ᴮ (sup (ℙ→fam β U .snd)) → b ∈ S

  Φ-closure : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
            → {ℓ″ : Level} (S : ℙ B ℓ″)
            → 𝒰 (o ⊔ ℓ′ ⊔ ℓ″)
  Φ-closure ϕ S = (a : Ob)
                → (b : B)
                → (b , a) ∈ ϕ
                → ((b' : B) → b' ≤ᴮ a → b' ∈ S)
                → b ∈ S

  data 𝓘 (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) : B → 𝒰 (o ⊔ ℓsuc ℓ′) where
    c-closed : (U : ℙ B ℓ′) → ({b : B} → b ∈ U → 𝓘 ϕ b)
             → (b : B) → b ≤ᴮ (sup (ℙ→fam β U .snd)) → 𝓘 ϕ b
    ϕ-closed : (a : Ob) → (b : B) → (b , a) ∈ ϕ
             → ((b' : B) → b' ≤ᴮ a → 𝓘 ϕ b')
             → 𝓘 ϕ b
    𝓘-trunc : (b : B) → is-prop (𝓘 ϕ b)

  instance
    H-Level-𝓘 : ∀{n} {ϕ} {b} ⦃ _ : 1 ≤ʰ n ⦄ → H-Level n (𝓘 ϕ b)
    H-Level-𝓘 ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (𝓘-trunc _)

  module trunc-ind-def (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) where

    𝓘nd : ℙ B (o ⊔ ℓsuc ℓ′)
    𝓘nd b = el! (𝓘 ϕ b)

    𝓘nd-is-c-closed : c-closure 𝓘nd
    𝓘nd-is-c-closed = c-closed

    𝓘nd-is-ϕ-closed : Φ-closure ϕ 𝓘nd
    𝓘nd-is-ϕ-closed = ϕ-closed

    𝓘nd-is-initial : {ℓ″ : Level} (P : ℙ B ℓ″)
                    → c-closure P
                    → Φ-closure ϕ P
                    → 𝓘nd ⊆ P
    𝓘nd-is-initial P cc ϕc (c-closed U sub b le) = cc U (λ ua → 𝓘nd-is-initial P cc ϕc (sub ua)) b le
    𝓘nd-is-initial P cc ϕc (ϕ-closed a b m f)    = ϕc a b m (λ b' le → 𝓘nd-is-initial P cc ϕc (f b' le))
    𝓘nd-is-initial P cc ϕc (𝓘-trunc b x y i)    = hlevel 1 (𝓘nd-is-initial P cc ϕc x) (𝓘nd-is-initial P cc ϕc y) i

module local-inductive-definitions
         {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h

  _↓_ : ℙ (B × Ob) (o ⊔ ℓ′) → Ob → 𝒰 (o ⊔ ℓ ⊔ ℓ′)
  φ ↓ a = Σ[ b ꞉ B ] ∃[ a' ꞉ Ob ] (b , a') ∈ φ × a' ≤ a

  ↓→base : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) → (a : Ob) → ϕ ↓ a → B
  ↓→base ϕ a = fst

  ↓-monotonicity-lemma : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
                       → (x y : Ob) → x ≤ y
                       → ϕ ↓ x → ϕ ↓ y
  ↓-monotonicity-lemma ϕ x y le (b , c) = b , map (second $ second $ _∙ le) c

  ↓-has-sup-implies-monotone : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
                             → (x y s s' : Ob) → x ≤ y
                             → is-lub P (β ∘ₜ ↓→base ϕ x) s
                             → is-lub P (β ∘ₜ ↓→base ϕ y) s'
                             → s ≤ s'
  ↓-has-sup-implies-monotone ϕ x y s s' le lu1 lu2 =
    lu1 .least s' $ lu2 .fam≤lub ∘ₜ ↓-monotonicity-lemma ϕ x y le

  is-local : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  is-local ϕ = (a : Ob) → is-of-size ℓ′ (ϕ ↓ a)

  module _ (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) (loc : is-local ϕ) where

    private
      S' : Ob → 𝒰 ℓ′
      S' a = ⌞ loc a ⌟

      S'≃↓ : (a : Ob) → S' a ≃ ϕ ↓ a
      S'≃↓ a = resizing-cond (loc a)

      S'→↓ : (a : Ob) → S' a → ϕ ↓ a
      S'→↓ a = S'≃↓ a $_

      ↓→S' : (a : Ob) → ϕ ↓ a → S' a
      ↓→S' a = S'≃↓ a ⁻¹ $_

      S'-monotone-ish : (x y : Ob) → x ≤ y
                      → S' x → S' y
      S'-monotone-ish x y o =
       ↓→S' y ∘ₜ ↓-monotonicity-lemma ϕ x y o ∘ₜ S'→↓ x

    Γ : P ⇒ P
    Γ .hom a = sup (β ∘ₜ fst ∘ₜ S'→↓ a)
    Γ .pres-≤ {x} {y} le =
      ↓-has-sup-implies-monotone ϕ x y _ _ le
         (sup-of-small-fam-is-lub L (β ∘ₜ ↓→base ϕ x) (loc x))
         (sup-of-small-fam-is-lub L (β ∘ₜ ↓→base ϕ y) (loc y))

  monotone-map-give-local-ind-def : (f : P ⇒ P)
                                  → Σ[ ϕ ꞉ ℙ (B × Ob) (o ⊔ ℓ′) ] Σ[ loc ꞉ is-local ϕ ] ((x : Ob) → Γ ϕ loc # x ＝ f # x)
  monotone-map-give-local-ind-def f = ϕ , loc , H
    where
      ϕ : ℙ (B × Ob) (o ⊔ ℓ′)
      ϕ (b , a) = el! (Lift o (b ≤ᴮ f # a))

      ↓ᴮf-equiv-↓-tot : (a : Ob) → small-↓ᴮ (f # a) ≃ (ϕ ↓ a)
      ↓ᴮf-equiv-↓-tot a =
        Σ-ap-snd λ b → prop-extₑ!
            (λ le → ∣ a , lift le , refl ∣₁)
            (elim! λ a' lo le' → ≤→≤ᴮ (≤ᴮ→≤ lo ∙ f .pres-≤ le'))

      loc : is-local ϕ
      loc a = small-↓ᴮ (f # a) , ↓ᴮf-equiv-↓-tot a

      G : (x : Ob) → is-lub P (β ∘ₜ ↓→base ϕ x) (f # x)
      G x .fam≤lub (b , e) = elim! (λ a' lo le' → ≤ᴮ→≤ lo ∙ f .pres-≤ le') e
      G x .least u' ub     = is-lubᴮ u' (ub ∘ₜ (↓ᴮf-equiv-↓-tot x $_))

      H : (x : Ob) → Γ ϕ loc # x ＝ f # x
      H x = equiv-reindexing refl (Γ ϕ loc # x) (f # x) (sup-of-small-fam-is-lub L (β ∘ₜ ↓→base ϕ x) (loc x)) (G x)

  ind-def-from-monotone-map : (f : P ⇒ P) → ℙ (B × Ob) (o ⊔ ℓ′)
  ind-def-from-monotone-map f = monotone-map-give-local-ind-def f .fst

  local-from-monotone-map : (f : P ⇒ P) → is-local (ind-def-from-monotone-map f)
  local-from-monotone-map f = monotone-map-give-local-ind-def f .snd .fst

  local-ind-def-is-section-of-Γ : (f : P ⇒ P)
                                → (x : Ob)
                                → Γ (ind-def-from-monotone-map f) (local-from-monotone-map f) # x ＝ f # x
  local-ind-def-is-section-of-Γ f = monotone-map-give-local-ind-def f .snd .snd

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open local-inductive-definitions P L β h

  module correspondance-from-locally-small-ϕ
           (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
           (loc : is-local ϕ)
        where

    is-small-closed-subset : ℙ B ℓ′ → 𝒰 (o ⊔ ℓsuc ℓ′)
    is-small-closed-subset S = c-closure P L β h S × Φ-closure P L β h ϕ S

    -- is-small-closed-subset-is-prop : (P : ℙ B ℓ′) → is-prop (is-small-closed-subset P)
    -- is-small-closed-subset-is-prop P = hlevel 1

    small-closed-subsets : 𝒰 (o ⊔ ℓsuc ℓ′)
    small-closed-subsets = Σ[ P ꞉ ℙ B ℓ′ ] is-small-closed-subset P

    is-deflationary : Ob → 𝒰 ℓ
    is-deflationary a = Γ ϕ loc # a ≤ a

    -- is-deflationary-is-prop : (a : Ob) → is-prop (is-deflationary a)
    -- is-deflationary-is-prop a = hlevel 1

    deflationary-points : 𝒰 (o ⊔ ℓ)
    deflationary-points = Σ[ a ꞉ Ob ] is-deflationary a

    small-closed-subsets→def-points : small-closed-subsets → deflationary-points
    small-closed-subsets→def-points (P , cc , φc) =
        sup-of-P
      , sup-of-small-fam-is-lub L (β ∘ₜ ↓→base ϕ sup-of-P) (loc sup-of-P) .least sup-of-P
          λ where (b , e) →
                    rec! (λ a p le →
                           suprema (ℙ→fam β P .snd) .fam≤lub
                             (b , φc a b p λ b' le' →
                                              cc P refl b' (≤→≤ᴮ (≤ᴮ→≤ le' ∙ le))))
                         e
      where
        sup-of-P : Ob
        sup-of-P = sup (ℙ→fam β P .snd)

    def-points→small-closed-subsets : deflationary-points → small-closed-subsets
    def-points→small-closed-subsets (a , isdef) =
      Q a , Q-c-closed , Q-φ-closed
      where
        Q : Ob → ℙ B ℓ′
        Q x b = el! (b ≤ᴮ x)

        sup-Q : Ob → Ob
        sup-Q x = sup (ℙ→fam β (Q x) .snd)

        is-sup-Q : (x : Ob) → sup-Q x ＝ x
        is-sup-Q x = is-supᴮ' ⁻¹

        Q-c-closed : c-closure P L β h (Q a)
        Q-c-closed U C b le = ≤→≤ᴮ
          $ ≤ᴮ→≤ le
          ∙ subst (sup (ℙ→fam β U .snd) ≤_) (is-sup-Q a)
              (joins-preserve-containment L β U (Q a) C)

        Q-φ-closed : Φ-closure P L β h ϕ (Q a)
        Q-φ-closed a' b p f = ≤→≤ᴮ
          $ sup-of-small-fam-is-lub L (β ∘ₜ ↓→base ϕ a) (loc a) .fam≤lub
              (b , ∣ a' , p , subst (_≤ a) (is-sup-Q a')
                                (subst (sup-Q a' ≤_) (is-sup-Q a)
                                   (joins-preserve-containment L β (Q a') (Q a) (λ {z} → f z))) ∣₁)
          ∙ isdef

    @0 small-closed-subsets≃def-points : small-closed-subsets ≃ deflationary-points
    small-closed-subsets≃def-points =
        small-closed-subsets→def-points
      , is-iso→is-equiv (iso def-points→small-closed-subsets ri li)
      where
      ri : def-points→small-closed-subsets is-right-inverse-of small-closed-subsets→def-points
      ri (a , isdef) = is-supᴮ' ⁻¹ ,ₚ prop!

      @0 li : def-points→small-closed-subsets is-left-inverse-of small-closed-subsets→def-points
      li (P , cc , φc)
        =  ext (λ b → cc P refl b , λ r → ≤→≤ᴮ (suprema (ℙ→fam β P .snd) .fam≤lub (b , r)))
        ,ₚ prop!

    open trunc-ind-def P L β h ϕ

    module smallness-assumption (j : (b : B) → is-of-size ℓ′ (b ∈ 𝓘nd)) where

      private

        𝓘' : B → 𝒰 ℓ′
        𝓘' b = ⌞ j b ⌟

        𝓘'≃𝓘nd : (b : B) → 𝓘' b ≃ b ∈ 𝓘nd
        𝓘'≃𝓘nd b = resizing-cond (j b)

        𝓘'→𝓘nd : (b : B) → 𝓘' b → b ∈ 𝓘nd
        𝓘'→𝓘nd b = 𝓘'≃𝓘nd b $_

        𝓘nd→𝓘' : (b : B) → b ∈ 𝓘nd → 𝓘' b
        𝓘nd→𝓘' b = 𝓘'≃𝓘nd b ⁻¹ $_

        𝓘'-is-prop : {b : B} → is-prop (𝓘' b)
        𝓘'-is-prop {b} = ≃→is-of-hlevel 1 (𝓘'≃𝓘nd b) (𝓘-trunc b)

        𝓘'-subset : ℙ B ℓ′
        𝓘'-subset b = el (𝓘' b) 𝓘'-is-prop

        𝓘'-is-c-closed : c-closure P L β h 𝓘'-subset
        𝓘'-is-c-closed U C b le = 𝓘nd→𝓘' b (𝓘nd-is-c-closed U (λ {x} → 𝓘'→𝓘nd x ∘ₜ C) b le)

        𝓘'-is-ϕ-closed : Φ-closure P L β h ϕ 𝓘'-subset
        𝓘'-is-ϕ-closed a b p f = 𝓘nd→𝓘' b (𝓘nd-is-ϕ-closed a b p (λ b' → 𝓘'→𝓘nd b' ∘ₜ f b'))

        total-space-𝓘-is-small : is-of-size ℓ′ Σ[ 𝓘nd ]
        total-space-𝓘-is-small = Σ[ 𝓘'-subset ] , Σ-ap-snd 𝓘'≃𝓘nd

        e : Σ[ 𝓘'-subset ] ≃ Σ[ 𝓘nd ]
        e = resizing-cond total-space-𝓘-is-small

        sup-𝓘 : Ob
        sup-𝓘 = sup {I = Σ[ 𝓘'-subset ]} (β ∘ₜ 𝕋→carrier 𝓘nd ∘ₜ (e $_))

        sup-𝓘-is-lub : is-lub P (ℙ→fam β 𝓘nd .snd) sup-𝓘
        sup-𝓘-is-lub = sup-of-small-fam-is-lub L (β ∘ₜ 𝕋→carrier 𝓘nd) total-space-𝓘-is-small

      sup-𝓘-is-fixed-point : Γ ϕ loc # sup-𝓘 ＝ sup-𝓘
      sup-𝓘-is-fixed-point =
        ≤-antisym Γ-sup-below-sup $
        subst (sup-𝓘 ≤_) sup-Q-is-Γ-sup sup-𝓘-below-sup-Q
        where
        Γ-sup-below-sup : Γ ϕ loc # sup-𝓘 ≤ sup-𝓘
        Γ-sup-below-sup =
          small-closed-subsets→def-points (𝓘'-subset , 𝓘'-is-c-closed , 𝓘'-is-ϕ-closed) .snd

        Q-Γ-sc-sub : small-closed-subsets
        Q-Γ-sc-sub = def-points→small-closed-subsets
          (Γ ϕ loc # sup-𝓘 , Γ ϕ loc .pres-≤ Γ-sup-below-sup)

        Q-Γ-sup : ℙ B ℓ′
        Q-Γ-sup = Q-Γ-sc-sub .fst
        Q-is-c-closed : c-closure P L β h Q-Γ-sup
        Q-is-c-closed = Q-Γ-sc-sub .snd .fst
        Q-is-ϕ-closed : Φ-closure P L β h ϕ Q-Γ-sup
        Q-is-ϕ-closed = Q-Γ-sc-sub .snd .snd

        sup-Q : Ob
        sup-Q = sup (ℙ→fam β Q-Γ-sup .snd)

        sup-Q-is-Γ-sup : sup-Q ＝ Γ ϕ loc # sup-𝓘
        sup-Q-is-Γ-sup = is-supᴮ' ⁻¹

        sup-𝓘-below-sup-Q : sup-𝓘 ≤ sup-Q
        sup-𝓘-below-sup-Q =
          joins-preserve-containment L β 𝓘'-subset Q-Γ-sup
            λ {x} → 𝓘nd-is-initial Q-Γ-sup Q-is-c-closed Q-is-ϕ-closed ∘ₜ 𝓘'→𝓘nd x


      sup-𝓘-is-least-fixed-point : (a : Ob)
                                 → Γ ϕ loc # a ＝ a → sup-𝓘 ≤ a
      sup-𝓘-is-least-fixed-point a p =
        subst (sup-𝓘 ≤_) sup-P-is-a sup-𝓘-below-sup-P
        where
          P-sc-sub : small-closed-subsets
          P-sc-sub = def-points→small-closed-subsets (a , subst (Γ ϕ loc # a ≤_) p refl)

          P-a : ℙ B ℓ′
          P-a = P-sc-sub .fst
          P-is-c-closed : c-closure P L β h P-a
          P-is-c-closed = P-sc-sub .snd .fst
          P-is-ϕ-closed : Φ-closure P L β h ϕ P-a
          P-is-ϕ-closed = P-sc-sub .snd .snd

          sup-P : Ob
          sup-P = sup (ℙ→fam β P-a .snd)

          sup-P-is-a : sup-P ＝ a
          sup-P-is-a = is-supᴮ' ⁻¹

          sup-𝓘-below-sup-P : sup-𝓘 ≤ sup-P
          sup-𝓘-below-sup-P =
            joins-preserve-containment L β 𝓘'-subset P-a
               λ {x} → 𝓘nd-is-initial P-a P-is-c-closed P-is-ϕ-closed ∘ₜ 𝓘'→𝓘nd x

      Γ-has-least-fixed-point : LFP P (Γ ϕ loc)
      Γ-has-least-fixed-point .LFP.fixpoint = sup-𝓘
      Γ-has-least-fixed-point .LFP.has-lfp .is-lfp.fixed = sup-𝓘-is-fixed-point
      Γ-has-least-fixed-point .LFP.has-lfp .is-lfp.least = sup-𝓘-is-least-fixed-point

module bounded-inductive-definitions {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open local-inductive-definitions P L β h

  _is-a-small-cover-of_ : ∀ {ℓ″} → 𝒰 ℓ′ → 𝒰 ℓ″ → 𝒰 (ℓ′ ⊔ ℓ″)
  X is-a-small-cover-of Y = X ↠ Y

  covering-cond : {ϕ : ℙ (B × Ob) (o ⊔ ℓ′)}
                → (T : 𝒰 ℓ′) → (T → 𝒰 ℓ′) → 𝒰 (o ⊔ ℓ ⊔ ℓ′)
  covering-cond {ϕ} T α = (a : Ob) → (b : B) → (b , a) ∈ ϕ
                        → ∃[ t ꞉ T ] α t is-a-small-cover-of ↓ᴮ P L β a

  has-a-bound : ℙ (B × Ob) (o ⊔ ℓ′) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  has-a-bound ϕ = Σ[ T ꞉ 𝒰 ℓ′ ] Σ[ α ꞉ (T → 𝒰 ℓ′) ] covering-cond {ϕ} T α

  is-bounded : ℙ (B × Ob) (o ⊔ ℓ′) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  is-bounded ϕ = ((a : Ob) → (b : B) → is-of-size ℓ′ ((b , a) ∈ ϕ)) × has-a-bound ϕ

  bounded→local : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
                → is-bounded ϕ → is-local ϕ
  bounded→local ϕ (ϕ-small , ϕ-has-bound) a =
    ≃→is-of-size! (≅ₜ→≃ (S₀→↓ , iso ↓→S₀ ri li))
    where
      T : 𝒰 ℓ′
      T = ϕ-has-bound .fst
      α : T → 𝒰 ℓ′
      α = ϕ-has-bound .snd .fst
      cov : covering-cond {ϕ} T α
      cov = ϕ-has-bound .snd .snd

      S₀ : 𝒰 (o ⊔ ℓ ⊔ ℓ′)
      S₀ = Σ[ b ꞉ B ] ∃[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ₜ m)) ∈ ϕ

      instance
        Size-α : ∀ {t} → Size ℓ′ (α t)
        Size-α {t} .Size.has-of-size = α t , refl
        {-# OVERLAPPING Size-α #-}

        Size-↓ᴮ : Size ℓ′ (↓ᴮ P L β a)
        Size-↓ᴮ .Size.has-of-size = ↓ᴮ-is-small

        Size-ϕ : {b : B} {z : Ob} → Size ℓ′ ((b , z) ∈ ϕ)
        Size-ϕ {b} {z} .Size.has-of-size = ϕ-small z b

      S₀→↓-aux : {b : B}
               → Σ[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ₜ m)) ∈ ϕ
               → Σ[ a' ꞉ Ob ] ((b , a') ∈ ϕ × a' ≤ a)
      S₀→↓-aux (t , m , p) =
          sup (↓ᴮ-inclusion P L β a ∘ₜ m) , p
        , suprema (↓ᴮ-inclusion P L β a ∘ₜ m) .least a (↓-is-sup a .fam≤lub ∘ₜ m)

      S₀→↓ : S₀ → ϕ ↓ a
      S₀→↓ = second (map S₀→↓-aux)

      g : {b : B} (a' : Ob) (p : (b , a') ∈ ϕ) (le : a' ≤ a)
        → Σ[ t ꞉ T ] α t is-a-small-cover-of ↓ᴮ P L β a'
        → Σ[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ₜ m)) ∈ ϕ
      g {b} a' p le (t , α-c) =
          t , g-m , subst (λ z → (b , z) ∈ ϕ) g-path p
        where
        g-m :  α t → ↓ᴮ P L β a
        g-m = ↓ᴮ-≤ P L β le ∘ₜ (α-c $_)
        g-path : a' ＝ sup (↓ᴮ-inclusion P L β a ∘ₜ g-m)
        g-path = cover-reindexing α-c a' (sup (↓ᴮ-inclusion P L β a ∘ₜ g-m)) (↓-is-sup a') (suprema (↓ᴮ-inclusion P L β a' ∘ₜ α-c .fst))

      cur-trunc-g : {b : B} (a' : Ob) (p : (b , a') ∈ ϕ) (le : a' ≤ a)
                  → ∃[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ₜ m)) ∈ ϕ
      cur-trunc-g {b} a' p le = map (g a' p le) (cov a' b p)

      ↓→S₀ : ϕ ↓ a → S₀
      ↓→S₀ = second (rec! cur-trunc-g)

      ri : ↓→S₀ is-right-inverse-of S₀→↓
      ri _ = trivial!

      li : ↓→S₀ is-left-inverse-of S₀→↓
      li _ = trivial!

module _ {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open bounded-inductive-definitions P L β h
  open small-presentation-of-lattice P L β h

  module small-QIT-from-bounded-and-small-presentation
           (small-pres : has-small-presentation)
           (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
           (bnd : is-bounded ϕ)
        where

    I₁ : 𝒰 ℓ′
    I₁ = small-pres .fst .fst
    Y : I₁ → ℙ B ℓ′
    Y = small-pres .fst .snd .fst
    R : ℙ (B × ℙ B ℓ′) ℓ′
    R = small-pres .fst .snd .snd
    is-small-pres : is-a-small-presentation (I₁ , Y , R)
    is-small-pres = small-pres .snd

    is-small-pres→ : (b : B) → (X : ℙ B ℓ′)
                   → b ≤ᴮ (sup (ℙ→fam β X .snd))
                   → ∃[ j ꞉ I₁ ] Y j ⊆ X × (b , Y j) ∈ R
    is-small-pres→ b X = is-small-pres b X $_

    is-small-pres← : (b : B) → (X : ℙ B ℓ′)
                   → ∃[ j ꞉ I₁ ] Y j ⊆ X × (b , Y j) ∈ R
                   → b ≤ᴮ (sup (ℙ→fam β X .snd))
    is-small-pres← b X = is-small-pres b X ⁻¹ $_

    ϕ-is-small : (a : Ob) → (b : B) → is-of-size ℓ′ ((b , a) ∈ ϕ)
    ϕ-is-small = bnd .fst

    small-ϕ : B → Ob → 𝒰 ℓ′
    small-ϕ b a = ϕ-is-small a b .fst

    small-ϕ≃ϕ : (a : Ob) → (b : B) → small-ϕ b a ≃ (b , a) ∈ ϕ
    small-ϕ≃ϕ a b = ϕ-is-small a b .snd

    small-ϕ→ϕ : (a : Ob) → (b : B) → small-ϕ b a → (b , a) ∈ ϕ
    small-ϕ→ϕ a b = small-ϕ≃ϕ a b $_

    ϕ→small-ϕ : (a : Ob) → (b : B) → (b , a) ∈ ϕ → small-ϕ b a
    ϕ→small-ϕ a b = small-ϕ≃ϕ a b ⁻¹ $_

    I₂ : 𝒰 ℓ′
    I₂ = bnd .snd .fst
    α : I₂ → 𝒰 ℓ′
    α = bnd .snd .snd .fst
    cover-condition : (a : Ob) → (b : B) → (b , a) ∈ ϕ
                    → ∃[ j ꞉ I₂ ] α j is-a-small-cover-of ↓ᴮ P L β a
    cover-condition = bnd .snd .snd .snd

    Small-c-closure : {ℓ″ : Level} (S : ℙ B ℓ″) → 𝒰 (ℓ′ ⊔ ℓ″)
    Small-c-closure S = (j : I₁)
                      → ((b : B) → b ∈ Y j → b ∈ S)
                      → (b : B) → (b , Y j) ∈ R
                      → b ∈ S

    Small-Φ-closure : {ℓ″ : Level} (S : ℙ B ℓ″) → 𝒰 (ℓ′ ⊔ ℓ″)
    Small-Φ-closure S = (j : I₂) → (m : α j → B) → (b : B)
                      → small-ϕ b (sup (β ∘ₜ m))
                      → ((b' : B) → b' ≤ᴮ sup (β ∘ₜ m) → b' ∈ S)
                      → b ∈ S

    data Small-𝓘 : B → 𝒰 ℓ′ where
      Small-c-closed : (j : I₁)
                     → ((b : B) → b ∈ Y j → Small-𝓘 b)
                     → (b : B) → (b , Y j) ∈ R
                     → Small-𝓘 b
      Small-ϕ-closed : (j : I₂) → (m : α j → B) → (b : B)
                      → small-ϕ b (sup (β ∘ₜ m))
                      → ((b' : B) → b' ≤ᴮ sup (β ∘ₜ m) → Small-𝓘 b')
                      → Small-𝓘 b
      Small-𝓘-trunc : (b : B) → is-prop (Small-𝓘 b)

    instance
      H-Level-Small-𝓘 : ∀{n} {b} ⦃ _ : 1 ≤ʰ n ⦄ → H-Level n (Small-𝓘 b)
      H-Level-Small-𝓘 ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (Small-𝓘-trunc _)

    module small-trunc-ind-def where

      Small-𝓘nd : ℙ B ℓ′
      Small-𝓘nd b = el! (Small-𝓘 b)

      Small-𝓘nd-is-c-closed : Small-c-closure Small-𝓘nd
      Small-𝓘nd-is-c-closed = Small-c-closed

      Small-𝓘nd-is-ϕ-closed : Small-Φ-closure Small-𝓘nd
      Small-𝓘nd-is-ϕ-closed = Small-ϕ-closed

      Small-𝓘nd-is-initial : {ℓ″ : Level} (P : ℙ B ℓ″)
                     → Small-c-closure P
                     → Small-Φ-closure P
                     → Small-𝓘nd ⊆ P
      Small-𝓘nd-is-initial P cc ϕc (Small-c-closed j sub b h)  =
        cc j (λ b₁ yjb → Small-𝓘nd-is-initial P cc ϕc (sub b₁ yjb)) b h
      Small-𝓘nd-is-initial P cc ϕc (Small-ϕ-closed j m b sf f) =
        ϕc j m b sf λ b' le → Small-𝓘nd-is-initial P cc ϕc (f b' le)
      Small-𝓘nd-is-initial P cc ϕc (Small-𝓘-trunc b x y i)     =
        hlevel 1 (Small-𝓘nd-is-initial P cc ϕc x) (Small-𝓘nd-is-initial P cc ϕc y) i

module _ {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open bounded-inductive-definitions P L β h
  open small-presentation-of-lattice P L β h

  module 𝓘nd-is-small-from-bounded-and-small-presentation
          (small-pres : has-small-presentation)
          (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
          (bnd : is-bounded ϕ)
         where

    open small-QIT-from-bounded-and-small-presentation P L β h small-pres ϕ bnd
    open trunc-ind-def P L β h ϕ
    open small-trunc-ind-def

    𝓘nd-⊆-Small-𝓘nd : 𝓘nd ⊆ Small-𝓘nd
    𝓘nd-⊆-Small-𝓘nd = 𝓘nd-is-initial Small-𝓘nd c-cl-sm Φ-cl-sm
      where
      c-cl-sm : c-closure P L β h Small-𝓘nd
      c-cl-sm U C b le =
        elim! {P = λ _ → ⌞ Small-𝓘nd b ⌟}
              (λ j C' r → Small-𝓘nd-is-c-closed j (λ b' → C ∘ₜ C') b r)
              (is-small-pres→ b U le)

      Φ-cl-sm : Φ-closure P L β h ϕ Small-𝓘nd
      Φ-cl-sm a b p C =
        ∥-∥₁.elim {P = λ _ → ⌞ Small-𝓘nd b ⌟}
                  (λ _ → Small-𝓘-trunc b)
                  u
                  (cover-condition a b p)
        where
        u : Σ[ i ꞉ I₂ ] α i is-a-small-cover-of ↓ᴮ P L β a → b ∈ Small-𝓘nd
        u (i₂ , s) = Small-𝓘nd-is-ϕ-closed i₂ (↓ᴮ→base P L β a ∘ₜ (s $_)) b
                                 (ϕ→small-ϕ (sup (↓ᴮ-inclusion P L β a ∘ₜ (s $_))) b
                                            (subst (λ q → (b , q) ∈ ϕ) a=⋁α p))
                                 λ b' → C b' ∘ₜ subst (b' ≤ᴮ_) (a=⋁α ⁻¹)
          where
          a=⋁α : a ＝ sup (↓ᴮ-inclusion P L β a ∘ₜ (s $_))
          a=⋁α = cover-reindexing s a (sup (↓ᴮ-inclusion P L β a ∘ₜ (s $_))) (↓-is-sup a) (suprema (↓ᴮ-inclusion P L β a ∘ₜ (s $_)))

    Small-𝓘nd-⊆-𝓘nd : Small-𝓘nd ⊆ 𝓘nd
    Small-𝓘nd-⊆-𝓘nd = Small-𝓘nd-is-initial 𝓘nd c-cl-sm Φ-cl-sm
      where
      c-cl-sm : Small-c-closure 𝓘nd
      c-cl-sm j C b r = 𝓘nd-is-c-closed (Y j) (λ {x} → C x) b
                          (is-small-pres← b (Y j) ∣ j , refl , r ∣₁)

      Φ-cl-sm : Small-Φ-closure 𝓘nd
      Φ-cl-sm j m b s C = 𝓘nd-is-ϕ-closed (sup (β ∘ₜ m)) b
                            (small-ϕ→ϕ (sup (β ∘ₜ m)) b s) C

    𝓘nd-is-small : (b : B) → is-of-size ℓ′ (b ∈ 𝓘nd)
    𝓘nd-is-small b =
        (b ∈ Small-𝓘nd)
      , prop-extₑ (hlevel 1) (𝓘-trunc b)
          Small-𝓘nd-⊆-𝓘nd 𝓘nd-⊆-Small-𝓘nd

module _ {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open local-inductive-definitions P L β h
  open bounded-inductive-definitions P L β h
  open small-presentation-of-lattice P L β h
  open small-QIT-from-bounded-and-small-presentation P L β h

  Untruncated-LFP-Theorem : has-small-presentation
                          → (f : P ⇒ P)
                          → Σ[ ϕ ꞉ ℙ (B × Ob) (o ⊔ ℓ′) ] Σ[ bnd ꞉ is-bounded ϕ ] ((x : Ob) → Γ ϕ (bounded→local ϕ bnd) # x ＝ f # x)
                          → LFP P f
  Untruncated-LFP-Theorem small-pres f (ϕ , bnd , H) = subst (LFP P) (ext H) Γ-has-least-fixed-point
    where
     open correspondance-from-locally-small-ϕ P L β h ϕ (bounded→local ϕ bnd)
     open 𝓘nd-is-small-from-bounded-and-small-presentation P L β h small-pres ϕ bnd
     open smallness-assumption 𝓘nd-is-small

  LFP-Theorem : has-small-presentation
              → (f : P ⇒ P)
              → ∃[ ϕ ꞉ ℙ (B × Ob) (o ⊔ ℓ′) ] Σ[ bnd ꞉ is-bounded ϕ ] ((x : Ob) → Γ ϕ (bounded→local ϕ bnd) # x ＝ f # x)
              → LFP P f
  LFP-Theorem small-pres f = ∥-∥₁.elim hlevel! (Untruncated-LFP-Theorem small-pres f)

module _ {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open local-inductive-definitions P L β h
  open bounded-inductive-definitions P L β h

  density-condition : (Ob → Ob) → (I : 𝒰 ℓ′) → (I → Ob)
                    → 𝒰 (o ⊔ ℓ ⊔ ℓ′)
  density-condition f I γ = (b : B) → (a : Ob) → b ≤ᴮ f a
                          → ∃[ i ꞉ I ] b ≤ᴮ f (γ i) × γ i ≤ a

  is-dense : (Ob → Ob) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  is-dense f = Σ[ I ꞉ 𝒰 ℓ′ ] Σ[ γ ꞉ (I → Ob) ] density-condition f I γ

  module _ (l-small : is-locally-of-size ℓ′ Ob) where

    private
      _＝ˢ_ : Ob → Ob → 𝒰 ℓ′
      x ＝ˢ y = ⌞ l-small x y ⌟

      =ˢ≃= : {x y : Ob} → x ＝ˢ y ≃ x ＝ y
      =ˢ≃= {x} {y} = resizing-cond (l-small x y)

      =ˢ→= : {x y : Ob} → x ＝ˢ y → x ＝ y
      =ˢ→= = =ˢ≃= $_

      =→=ˢ : {x y : Ob} → x ＝ y → x ＝ˢ y
      =→=ˢ = =ˢ≃= ⁻¹ $_

      =ˢ-refl : {x : Ob} → x ＝ˢ x
      =ˢ-refl = =→=ˢ refl

    dense→bounded : (f : P ⇒ P)
                  → is-dense (f $_)
                  → Σ[ ϕ ꞉ ℙ (B × Ob) (o ⊔ ℓ′) ] Σ[ bnd ꞉ is-bounded ϕ ] ((x : Ob) → Γ ϕ (bounded→local ϕ bnd) # x ＝ f # x)
    dense→bounded f (I , γ , f-dense) =
      φ , bnd , H
      where
      φ : ℙ (B × Ob) (o ⊔ ℓ′)
      φ (b , a') = el! (Lift {ℓ = ℓ′} o (∃[ i ꞉ I ] b ≤ᴮ f # (γ i) × γ i ＝ˢ a'))

      ϕ-small : (a : Ob) → (b : B) → is-of-size ℓ′ ((b , a) ∈ φ)
      ϕ-small a b = (∃[ i ꞉ I ] b ≤ᴮ f # (γ i) × γ i ＝ˢ a) , lift≃id ⁻¹

      ccond : covering-cond {ϕ = φ} I (small-↓ᴮ ∘ₜ γ)
      ccond a b = map (second λ {i} → (≃→↠ ∘ₜ λ where (o , eq) →
                                                       subst (λ q → small-↓ᴮ (γ i) ≃ ↓ᴮ P L β q)
                                                             (=ˢ→= eq)
                                                             small-↓ᴮ-≃-↓ᴮ))
                ∘ₜ (lift≃id $_)

      bnd : is-bounded φ
      bnd = ϕ-small , I , small-↓ᴮ ∘ₜ γ , ccond

      ↓ᴮ-fa→↓ : {a : Ob} {b : B}
             → b ≤ᴮ f # a
             → ∃[ a' ꞉ Ob ] (b , a') ∈ φ × a' ≤ a
      ↓ᴮ-fa→↓ {a} {b} = map (λ (i , o , r) →
                                  γ i , (lift≃id ⁻¹ $ ∣ i , o , =ˢ-refl ∣₁) , r)
                      ∘ₜ f-dense b a

      ↓→↓ᴮ-fa : {a : Ob} {b : B}
              → ∃[ a' ꞉ Ob ] (b , a') ∈ φ × a' ≤ a
              → b ≤ᴮ f # a
      ↓→↓ᴮ-fa {a} {b}
        = map (second $ first $ (lift≃id $_))
        ∙ elim! λ _ _ r path o → ≤→≤ᴮ (subst (β b ≤_) (ap$ f (=ˢ→= path)) (≤ᴮ→≤ r) ∙ f .pres-≤ o)

      ↓ᴮ-fa≃↓ : {a : Ob} → small-↓ᴮ (f # a) ≃ φ ↓ a
      ↓ᴮ-fa≃↓ = Σ-ap-snd λ b → prop-extₑ! ↓ᴮ-fa→↓ ↓→↓ᴮ-fa

      H : (a : Ob) → Γ φ (bounded→local φ bnd) # a ＝ f # a
      H a = equiv-reindexing ↓ᴮ-fa≃↓ (Γ φ (bounded→local φ bnd) # a) (f # a) (sup-of-small-fam-is-lub L (β ∘ₜ ↓→base φ a) (bounded→local φ bnd a)) is-supᴮ

module _ {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Order.Reasoning P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open bounded-inductive-definitions P L β h
  open small-presentation-of-lattice P L β h
  open small-QIT-from-bounded-and-small-presentation P L β h

  LFP-Theorem-from-Density : has-small-presentation
                           → is-locally-of-size ℓ′ Ob
                           → (f : P ⇒ P)
                           → is-dense P L β h (f $_)
                           → LFP P f
  LFP-Theorem-from-Density small-pres l-small f f-dense =
    Untruncated-LFP-Theorem P L β h small-pres f
      (dense→bounded P L β h l-small f f-dense)
