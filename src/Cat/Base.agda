{-# OPTIONS --safe --no-exact-split #-}
module Cat.Base where

open import Meta.Prelude
  hiding (id ; _∘_)
open import Meta.Projection
open import Meta.Reflection.Base

open import Structures.n-Type

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Term
open import Data.Unit.Base

record Precategory (o h : Level) : Type (ℓsuc (o ⊔ h)) where
  -- no-eta-equality
  -- ^ this sucks, gonna wait for agda issue #6721
  infixr 40 _∘_
  field
    Ob  : Type o
    Hom : Ob → Ob → Type h
    Hom-set : (x y : Ob) → is-set (Hom x y)
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

  opaque
    hom-set′ : ∀ {x y} → is-set (Hom x y)
    hom-set′ = Hom-set _ _

    instance
      H-Level-Hom : ∀ {x y} {k} → H-Level (2 + k) (Hom x y)
      H-Level-Hom = hlevel-basic-instance 2 hom-set′

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

private variable o h : Level

open Precategory

instance
  Underlying-precat : Underlying (Precategory o h)
  Underlying-precat {o} .Underlying.ℓ-underlying = o
  Underlying-precat .Underlying.⌞_⌟ = Ob

  open Struct-proj-desc

  hlevel-proj-precat : Struct-proj-desc true (quote Precategory.Hom)
  hlevel-proj-precat .has-level = quote hom-set′
  hlevel-proj-precat .upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-precat .get-level _ = pure (lit (nat 2))
  hlevel-proj-precat .get-argument (_ ∷ _ ∷ x v∷ _) = pure x
  hlevel-proj-precat .get-argument _ = type-error []

  Dual-Cat : Has-unary-op (Precategory o h)
  Dual-Cat .minv C .Ob = Ob C
  Dual-Cat .minv C .Hom x y = Hom C y x
  Dual-Cat .minv C .Hom-set x y = Hom-set C y x
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
  ⊤-Cat .⊤ .Hom-set _ _ = hlevel 2
  ⊤-Cat .⊤ .id = _
  ⊤-Cat .⊤ ._∘_ _ _ = _
  ⊤-Cat .⊤ .id-l _ = refl
  ⊤-Cat .⊤ .id-r _ = refl
  ⊤-Cat .⊤ .assoc _ _ _ = refl

Sets : (o : Level) → Precategory (ℓsuc o) o
Sets o .Ob = Set o
Sets _ .Hom A B = ⌞ A ⇒ B ⌟
Sets _ .Hom-set _ = hlevel!
Sets _ .id x = x
Sets _ ._∘_ f g x = f (g x)
Sets _ .id-l _ = refl
Sets _ .id-r _ = refl
Sets _ .assoc _ _ _ = refl
