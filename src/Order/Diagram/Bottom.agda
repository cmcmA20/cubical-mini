open import Categories.Diagram.Initial
open import Categories.Prelude

open import Data.Empty

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category

import Order.Reasoning

module Order.Diagram.Bottom {o ℓ} (P : Poset o ℓ) where

open Order.Reasoning P

open is-lub
open Lub

is-bottom : Ob → Type _
is-bottom bot = ∀ x → bot ≤ x

record Bottom : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    bot : Ob
    has-bottom : is-bottom bot

  ¡ : ∀ {x} → bot ≤ x
  ¡ = has-bottom _

is-bottom→is-lub : ∀ {lub} {f : ⊥ → _} → is-bottom lub → is-lub P f lub
is-bottom→is-lub is-bot .least x _ = is-bot x

is-lub→is-bottom : ∀ {lub} {f : ⊥ → _} → is-lub P f lub → is-bottom lub
is-lub→is-bottom lub x = lub .least x λ ()

is-bottom-is-prop : ∀ x → is-prop (is-bottom x)
is-bottom-is-prop _ = hlevel 1

bottom-unique : ∀ {x y} → is-bottom x → is-bottom y → x ＝ y
bottom-unique p q = ≤-antisym (p _) (q _)

Bottom-is-prop : is-prop Bottom
Bottom-is-prop p q i .Bottom.bot =
  bottom-unique (Bottom.has-bottom p) (Bottom.has-bottom q) i
Bottom-is-prop p q i .Bottom.has-bottom =
  is-prop→pathᴾ
    (λ i → is-bottom-is-prop (bottom-unique (Bottom.has-bottom p) (Bottom.has-bottom q) i))
    (Bottom.has-bottom p) (Bottom.has-bottom q) i

instance
  H-Level-Bottom
    : ∀ {n}
    → H-Level (suc n) Bottom 
  H-Level-Bottom = hlevel-basic-instance 1 Bottom-is-prop

Bottom→Lub : ∀ {f : ⊥ → _} → Bottom → Lub P f
Bottom→Lub bottom .Lub.lub = Bottom.bot bottom
Bottom→Lub bottom .Lub.has-lub = is-bottom→is-lub (Bottom.has-bottom bottom)

Lub→Bottom : ∀ {f : ⊥ → _} → Lub P f → Bottom
Lub→Bottom lub .Bottom.bot = Lub.lub lub
Lub→Bottom lub .Bottom.has-bottom = is-lub→is-bottom (Lub.has-lub lub)

is-bottom≃is-lub : ∀ {lub} {f} → is-equiv (is-bottom→is-lub {lub} {f})
is-bottom≃is-lub = biimp-is-equiv! _ is-lub→is-bottom

Bottom≃Lub : ∀ {f} → is-equiv (Bottom→Lub {f})
Bottom≃Lub = biimp-is-equiv! _ Lub→Bottom

is-bottom→initial : ∀ {x} → is-bottom x → is-initial (poset→precategory P) x
is-bottom→initial is-bot x .fst   = is-bot x
is-bottom→initial is-bot x .snd _ = ≤-thin _ _

initial→is-bottom : ∀ {x} → is-initial (poset→precategory P) x → is-bottom x
initial→is-bottom initial x = initial x .fst

