{-# OPTIONS --safe #-}
module Order.Constructions.Bool where

open import Cat.Prelude
open import Order.Base
open import Order.Complemented
open import Order.Constructions.Minmax
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Lattice
open import Order.Strict
open import Order.Total
open import Order.Ordinal

open import Data.Acc.Base
open import Data.Reflects.Base
open import Data.Dec.Base
open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Bool.Properties
open import Data.Sum.Base

-- false < true

_<bool_ : Bool → Bool → 𝒰
x <bool y = ⌞ not x and y ⌟

<bool-trans : ∀ {x y z} → x <bool y → y <bool z → x <bool z
<bool-trans {x} nxy nyz = and-so-l {x = not x} nxy × and-so-r nyz

Boolᶜᵖ : ComplementedPoset 0ℓ 0ℓ
Boolᶜᵖ .ComplementedPoset.Ob = Bool
Boolᶜᵖ .ComplementedPoset._≤_ x y = ⌞ x implies y ⌟
Boolᶜᵖ .ComplementedPoset._<_ = _<bool_
Boolᶜᵖ .ComplementedPoset.≤-thin = hlevel!
Boolᶜᵖ .ComplementedPoset.≤-refl {x} =
  true→so! ⦃ reflects-implies ⦄ λ x → x
Boolᶜᵖ .ComplementedPoset.≤-trans xy yz =
  true→so! ⦃ reflects-implies ⦄ λ x →
    so→true! ⦃ reflects-implies ⦄ yz $ so→true! ⦃ reflects-implies ⦄ xy $ x
Boolᶜᵖ .ComplementedPoset.≤-antisym {x = false} {y = false} _ _ = refl
Boolᶜᵖ .ComplementedPoset.≤-antisym {x = false} {y = true}  _   = false!
Boolᶜᵖ .ComplementedPoset.≤-antisym {x = true}  {y = false}     = false!
Boolᶜᵖ .ComplementedPoset.≤-antisym {x = true}  {y = true}  _ _ = refl
Boolᶜᵖ .ComplementedPoset.<-thin = hlevel!
Boolᶜᵖ .ComplementedPoset.<-irrefl {x} =
  so-not $
  subst (λ q → So (not q))
        (and-compl x ⁻¹ ∙ and-comm x _)
  oh
Boolᶜᵖ .ComplementedPoset.<-trans {x} = <bool-trans {x}
Boolᶜᵖ .ComplementedPoset.dec-≤ = Dec-So
Boolᶜᵖ .ComplementedPoset.dec-< = Dec-So
Boolᶜᵖ .ComplementedPoset.has-discrete = auto
Boolᶜᵖ .ComplementedPoset.≤≃≯ {x} {y} =
    =→≃ (ap So (  implies-not-or _ _ ⁻¹
                ∙ or-comm _ y
                ∙ ap (_or not x) (not-invol _ ⁻¹)
                ∙ not-and _ x ⁻¹))
  ∙ not-so-≃
Boolᶜᵖ .ComplementedPoset.<≃≱ {x} {y} =
  =→≃ (ap So (  and-comm _ y
              ∙ ap (_and not x) (not-invol _ ⁻¹)
              ∙ not-or _ x ⁻¹
              ∙ ap not (implies-not-or _ _)))
  ∙ not-so-≃

open ComplementedPoset

Boolₚ : Poset 0ℓ 0ℓ
Boolₚ = complemented→poset Boolᶜᵖ

ℕ-dec-total : is-decidable-total-order Boolₚ
ℕ-dec-total = has-dec-total-order Boolᶜᵖ

ℕ-total : is-total-order Boolₚ
ℕ-total = is-decidable-total-order.has-is-total ℕ-dec-total

instance
  Bool-bottom : Bottom Boolₚ
  Bool-bottom .Bottom.bot = false
  Bool-bottom .Bottom.bot-is-bot _ = oh

  Bool-top : Top Boolₚ
  Bool-top .Top.top = true
  Bool-top .Top.top-is-top _ =
    true→so! ⦃ reflects-implies ⦄ λ _ → oh

  Bool-joins : Has-joins Boolₚ
  Bool-joins {x} {y} .Join.lub = x or y
  Bool-joins .Join.has-join .is-join.l≤join =
    true→so! ⦃ reflects-implies ⦄ or-so-l
  Bool-joins .Join.has-join .is-join.r≤join =
    true→so! ⦃ reflects-implies ⦄ or-so-r
  Bool-joins .Join.has-join .is-join.least z xz yz =
    true→so! ⦃ reflects-implies ⦄ λ sxy →
    [ so→true! ⦃ reflects-implies ⦄ xz
    , so→true! ⦃ reflects-implies ⦄ yz
    ]ᵤ (or-so-elim sxy)

  Bool-meets : Has-meets Boolₚ
  Bool-meets {x} {y} .Meet.glb = x and y
  Bool-meets .Meet.has-meet .is-meet.meet≤l =
    true→so! ⦃ reflects-implies ⦄ and-so-l
  Bool-meets .Meet.has-meet .is-meet.meet≤r =
    true→so! ⦃ reflects-implies ⦄ and-so-r
  Bool-meets .Meet.has-meet .is-meet.greatest z zx zy =
    true→so! ⦃ reflects-implies ⦄ λ sz →
        so→true! ⦃ reflects-implies ⦄ zx sz
      × so→true! ⦃ reflects-implies ⦄ zy sz

  Bool-join-slat : is-join-semilattice Boolₚ
  Bool-join-slat .is-join-semilattice.has-bottom = Bool-bottom
  Bool-join-slat .is-join-semilattice.has-joins  = Bool-joins

  Bool-meet-slat : is-meet-semilattice Boolₚ
  Bool-meet-slat .is-meet-semilattice.has-top   = Bool-top
  Bool-meet-slat .is-meet-semilattice.has-meets = Bool-meets

  Bool-lat : is-lattice Boolₚ
  Bool-lat .is-lattice.has-join-slat = Bool-join-slat
  Bool-lat .is-lattice.has-meet-slat = Bool-meet-slat

Boolₛ : StrictPoset 0ℓ 0ℓ
Boolₛ = complemented→strict Boolᶜᵖ

<bool-wf : is-wf _<bool_
<bool-wf false = acc λ y sy → false! $ subst So (and-absorb-r _) sy
<bool-wf true  = acc λ where
                        false sy → acc λ z sz → false! $ subst So (and-absorb-r _) sz

<bool-lext : ∀ {x y} → (∀ z → (z <bool x) ≃ (z <bool y)) → x ＝ y
<bool-lext {x = false} {y = false} f = refl
<bool-lext {x = false} {y = true}  f = false! (f false ⁻¹ $ oh)
<bool-lext {x = true}  {y = false} f = false! (f false $ oh)
<bool-lext {x = true}  {y = true}  f = refl

Boolw : WESet 0ℓ 0ℓ
Boolw .WESet.Ob = Bool
Boolw .WESet._<_ = _<bool_
Boolw .WESet.<-thin = hlevel!
Boolw .WESet.<-wf = <bool-wf
Boolw .WESet.<-lext = <bool-lext

Boolω : Ordinal 0ℓ
Boolω = Boolw , λ {x} → <bool-trans {x}
