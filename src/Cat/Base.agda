{-# OPTIONS --safe --no-exact-split #-}
module Cat.Base where

open import Meta.Prelude
  hiding (id ; _∘_)

open import Structures.n-Type

open import Data.Empty.Base
open import Data.Unit.Base

-- I guess this would be called a wild precategry on 1lab
record Precategory (o h : Level) : Type (ℓsuc (o ⊔ h)) where
  -- no-eta-equality
  -- ^ this sucks, gonna wait for agda issue #6721
  infixr 40 _∘_
  field
    Ob  : Type o
    Hom : Ob → Ob → Type h
    id   : ∀ {x} → Hom x x
    _∘_  : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    id-l : ∀ {x y} (f : Hom x y) → id ∘ f ＝ f
    id-r : ∀ {x y} (f : Hom x y) → f ∘ id ＝ f
    assoc : ∀ {w x y z} (h : Hom w x) (g : Hom x y) (f : Hom y z)
          → (f ∘ g) ∘ h ＝ f ∘ (g ∘ h)

  Mor : Type (o ⊔ h)
  Mor = Σ[ a ꞉ Ob ] Σ[ b ꞉ Ob ] Hom a b

  Hom→Mor : ∀{a b} → Hom a b → Mor
  Hom→Mor f = _ , _ , f

  Mor-path : {f g : Mor}
           → (p : f .fst ＝ g .fst)
           → (q : f .snd .fst ＝ g .snd .fst)
           → ＜ f .snd .snd ／ (λ i → Hom (p i) (q i)) ＼ g .snd .snd ＞
           → f ＝ g
  Mor-path p q r i = p i , q i , r i

  instance
    Refl-Hom : Refl Hom
    Refl-Hom .refl = id
    {-# OVERLAPPING Refl-Hom #-}

    Trans-Hom : Trans Hom
    Trans-Hom ._∙_ f g = g ∘ f
    {-# OVERLAPPING Trans-Hom #-}

    HAssoc-Hom : HAssoc Hom
    HAssoc-Hom .∙-assoc = assoc
    {-# OVERLAPPING HAssoc-Hom #-}

    HUnit-o-Hom : HUnit-o Hom
    HUnit-o-Hom .∙-id-o = id-r
    {-# OVERLAPPING HUnit-o-Hom #-}

    HUnit-i-Hom : HUnit-i Hom
    HUnit-i-Hom .∙-id-i = id-l
    {-# OVERLAPPING HUnit-i-Hom #-}

    ⇒-Hom : ⇒-notation Ob Ob (𝒰 h)
    ⇒-Hom .⇒-notation.Constraint _ _ = ⊤
    ⇒-Hom ._⇒_ x y = Hom x y
    {-# OVERLAPPING ⇒-Hom #-}

    ≅-Cat-Ob : ≅-notation Ob Ob (𝒰 h)
    ≅-Cat-Ob ._≅_ = HIso Hom
    {-# OVERLAPPING ≅-Cat-Ob #-}

    ≊-Cat-Ob : ≊-notation Ob Ob (𝒰 h)
    ≊-Cat-Ob ._≊_ = HBiinv Hom
    {-# OVERLAPPING ≊-Cat-Ob #-}

private variable o h : Level

open Precategory

instance
  Underlying-precat : Underlying (Precategory o h)
  Underlying-precat {o} .Underlying.ℓ-underlying = o
  Underlying-precat .Underlying.⌞_⌟ = Ob

  Dual-Cat : Has-unary-op (Precategory o h)
  Dual-Cat .minv C .Ob = Ob C
  Dual-Cat .minv C .Hom x y = Hom C y x
  Dual-Cat .minv C .id = C .id
  Dual-Cat .minv C ._∘_ f g = C ._∘_ g f
  Dual-Cat .minv C .id-l = C .id-r
  Dual-Cat .minv C .id-r = C .id-l
  Dual-Cat .minv C .assoc f g h i = assoc C h g f (~ i)

  Invol-Dual-Cat : Invol (Precategory o h)
  Invol-Dual-Cat .minv-invol _ = refl

  ⊥-Cat : ⊥-notation (Precategory o h)
  ⊥-Cat .⊥ .Ob = ⊥
  ⊥-Cat .⊥ .Hom _ _ = ⊥

  ⊤-Cat : ⊤-notation (Precategory o h)
  ⊤-Cat .⊤ .Ob = ⊤
  ⊤-Cat .⊤ .Hom _ _ = ⊤
  ⊤-Cat .⊤ .id = _
  ⊤-Cat .⊤ ._∘_ _ _ = _
  ⊤-Cat .⊤ .id-l _ = refl
  ⊤-Cat .⊤ .id-r _ = refl
  ⊤-Cat .⊤ .assoc _ _ _ = refl

Types : (o : Level) → Precategory (ℓsuc o) o
Types o .Ob = Type o
Types _ .Hom = Fun
Types _ .id x = x
Types _ ._∘_ f g x = f (g x)
Types _ .id-l _ = refl
Types _ .id-r _ = refl
Types _ .assoc _ _ _ = refl

n-Types : (o : Level) (n : HLevel) → Precategory (ℓsuc o) o
n-Types o n .Ob = n-Type o n
n-Types _ _ .Hom A B = ⌞ A ⇒ B ⌟
n-Types _ _ .id x = x
n-Types _ _ ._∘_ f g x = f (g x)
n-Types _ _ .id-l _ = refl
n-Types _ _ .id-r _ = refl
n-Types _ _ .assoc _ _ _ = refl

Sets : (o : Level) → Precategory (ℓsuc o) o
Sets o = n-Types o 2
