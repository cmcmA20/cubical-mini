{-# OPTIONS --safe #-}
module Categories.Base where

open import Meta.Prelude
  hiding (id ; _∘_)

open import Meta.Effect.Idiom
open import Meta.Extensionality
open import Meta.Deriving.HLevel
open import Meta.Literals.FromNat
open import Meta.Projection
open import Meta.Record
open import Meta.Reflection.Base

open import Structures.n-Type

open import Data.Bool.Base

open import Functions.Embedding using (Injective)

open import Truncation.Propositional.Base

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
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (h : Hom w x)
          → f ∘ (g ∘ h) ＝ (f ∘ g) ∘ h

  Mor : Type (o ⊔ h)
  Mor = Σ[ a ꞉ Ob ] Σ[ b ꞉ Ob ] Hom a b

  Hom→Mor : ∀{a b} → Hom a b → Mor
  Hom→Mor f = _ , _ , f

  Mor-path : {f g : Mor}
           → (p : f .fst ＝ g .fst)
           → (q : f .snd .fst ＝ g .snd .fst)
           → Pathᴾ (λ i → Hom (p i) (q i)) (f .snd .snd) (g .snd .snd)
           → f ＝ g
  Mor-path p q r i = p i , q i , r i

  hom-set′ : ∀ {x y} → is-set (Hom x y)
  hom-set′ = Hom-set _ _

  instance
    H-Level-Hom : ∀ {x y} {k} → H-Level (2 + k) (Hom x y)
    H-Level-Hom = hlevel-basic-instance 2 hom-set′


private variable
  o h ℓ o′ h′ ℓ′ oᶜ hᶜ oᵈ hᵈ oᵉ hᵉ : Level
  C : Precategory oᶜ hᵈ
  D : Precategory oᵈ hᵈ

open Precategory

instance
  Underlying-precat : Underlying (Precategory o h)
  Underlying-precat {o} .Underlying.ℓ-underlying = o
  Underlying-precat .Underlying.⌞_⌟⁰ = Ob

  open Struct-proj-desc

  hlevel-proj-precat : Struct-proj-desc true (quote Precategory.Hom)
  hlevel-proj-precat .has-level = quote hom-set′
  hlevel-proj-precat .upwards-closure = quote is-of-hlevel-≤
  hlevel-proj-precat .get-level _ = pure (lit (nat 2))
  hlevel-proj-precat .get-argument (_ ∷ _ ∷ x v∷ _) = pure x
  hlevel-proj-precat .get-argument _ = type-error []


infixl 60 _ᵒᵖ
_ᵒᵖ : Precategory o h → Precategory o h
(C ᵒᵖ) .Ob = Ob C
(C ᵒᵖ) .Hom x y = Hom C y x
(C ᵒᵖ) .Hom-set x y = Hom-set C y x
(C ᵒᵖ) .id = id C
(C ᵒᵖ) ._∘_ f g = C ._∘_ g f
(C ᵒᵖ) .id-l x = C .id-r x
(C ᵒᵖ) .id-r x = C .id-l x
(C ᵒᵖ) .assoc f g h i = assoc C h g f (~ i)

precat-double-dual : {C : Precategory oᶜ hᶜ} → C ᵒᵖ ᵒᵖ ＝ C
precat-double-dual = refl

Sets : (o : Level) → Precategory (ℓsuc o) o
Sets o .Ob = Set o
Sets _ .Hom A B = A →̇ B
Sets _ .Hom-set _ = hlevel!
Sets _ .id x = x
Sets _ ._∘_ f g x = f (g x)
Sets _ .id-l _ = refl
Sets _ .id-r _ = refl
Sets _ .assoc _ _ _ = refl


-- Functors

record Functor
    (C : Precategory oᶜ hᶜ) (D : Precategory oᵈ hᵈ)
  : Type (oᶜ ⊔ hᶜ ⊔ oᵈ ⊔ hᵈ) where
  no-eta-equality

  private
    module C = Precategory C
    module D = Precategory D

  field
    F₀ : C.Ob → D.Ob
    F₁ : ∀ {x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)
    F-id : ∀ {x} → F₁ (C.id {x}) ＝ D.id
    F-∘ : ∀ {x y z} (f : C.Hom y z) (g : C.Hom x y)
        → F₁ (f C.∘ g) ＝ F₁ f D.∘ F₁ g

  -- Alias for F₀ for use in Functor record modules.
  ₀ = F₀

  -- Alias for F₁ for use in Functor record modules.
  ₁ = F₁

  op : Functor (C ᵒᵖ) (D ᵒᵖ)
  F₀ op      = F₀
  F₁ op      = F₁
  F-id op    = F-id
  F-∘ op f g = F-∘ g f

unquoteDecl functor-iso = declare-record-iso functor-iso (quote Functor)

instance
  Funlike-Functor
    : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    → Funlike ur (Functor C D) ⌞ C ⌟ (λ _ → ⌞ D ⌟)
  Funlike-Functor ._#_ = Functor.₀

functor-double-dual : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {F : Functor C D}
                    → Functor.op (Functor.op F) ＝ F
functor-double-dual {F} i .Functor.F₀ = F .Functor.F₀
functor-double-dual {F} i .Functor.F₁ = F .Functor.F₁
functor-double-dual {F} i .Functor.F-id = F .Functor.F-id
functor-double-dual {F} i .Functor.F-∘ = F .Functor.F-∘

_∘ᶠ_ : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {E : Precategory oᵉ hᵉ}
     → Functor D E → Functor C D → Functor C E
_∘ᶠ_ {C} {D} {E} F G = comps
  module F∘ where
    module C = Precategory C
    module D = Precategory D
    module E = Precategory E

    module F = Functor F
    module G = Functor G

    F₀ : C.Ob → E.Ob
    F₀ x = F.₀ (G.₀ x)

    F₁ : {x y : C.Ob} → C.Hom x y → E.Hom (F₀ x) (F₀ y)
    F₁ f = F.₁ (G.₁ f)

    opaque
      F-id : {x : C.Ob} → F₁ (C.id {x}) ＝ E.id {F₀ x}
      F-id =
          F.₁ (G.₁ C.id) ＝⟨ ap F.₁ G.F-id ⟩
          F.₁ D.id       ＝⟨ F.F-id ⟩
          E.id           ∎

      F-∘ : {x y z : C.Ob} (f : C.Hom y z) (g : C.Hom x y)
          → F₁ (f C.∘ g) ＝ (F₁ f E.∘ F₁ g)
      F-∘ f g =
          F.₁ (G.₁ (f C.∘ g))   ＝⟨ ap F.₁ (G.F-∘ f g) ⟩
          F.₁ (G.₁ f D.∘ G.₁ g) ＝⟨ F.F-∘ _ _ ⟩
          F₁ f E.∘ F₁ g         ∎

    comps : Functor _ _
    comps .Functor.F₀ = F₀
    comps .Functor.F₁ = F₁
    comps .Functor.F-id = F-id
    comps .Functor.F-∘ = F-∘

{-# DISPLAY F∘.comps F G = F ∘ᶠ G #-}

Id : {C : Precategory oᶜ hᶜ} → Functor C C
Functor.F₀ Id x = x
Functor.F₁ Id f = f
Functor.F-id Id = refl
Functor.F-∘ Id _ _ = refl


-- basic properties of functors

is-full : Functor C D → Type _
is-full {C} {D} F =
    {x y : C.Ob} (g : D.Hom (F.₀ x) (F.₀ y))
  → ∃[ f ꞉ C.Hom x y ] (F.₁ f ＝ g)
    where
      module C = Precategory C
      module D = Precategory D
      module F = Functor F

is-faithful : Functor C D → Type _
is-faithful {C} F = {x y : C.Ob} → Injective (F.₁ {x} {y})
  where
    module C = Precategory C
    module F = Functor F

is-fully-faithful : Functor C D → Type _
is-fully-faithful {C} F = {x y : C.Ob} → is-equiv (F.₁ {x} {y})
  where
    module C = Precategory C
    module F = Functor F


-- Natural transformations

record _⇒_ {C : Precategory oᶜ hᶜ}
           {D : Precategory oᵈ hᵈ}
           (F G : Functor C D)
      : Type (oᶜ ⊔ hᶜ ⊔ hᵈ)
  where
  no-eta-equality
  constructor NT
  private
    module F = Functor F
    module G = Functor G
    module D = Precategory D
    module C = Precategory C

  field
    η : ∀ x → D.Hom (F.₀ x) (G.₀ x)
    is-natural : ∀ x y → (f : C.Hom x y)
               → η y D.∘ F.₁ f ＝ G.₁ f D.∘ η x

  op : Functor.op G ⇒ Functor.op F
  op .η = η
  op .is-natural x y f = is-natural y x f ⁻¹

{-# INLINE NT #-}

unquoteDecl H-Level-Nat = declare-record-hlevel 2 H-Level-Nat (quote _⇒_)

instance
  Funlike-natural-transformation
    : {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {F G : Functor C D}
    → Funlike ur (F ⇒ G) ⌞ C ⌟ (λ x → D .Precategory.Hom (F $ x) (G $ x))
  Funlike-natural-transformation ._#_ = _⇒_.η

is-natural-transformation
  : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
  → (F G : Functor C D)
  → (η : ∀ x → D .Hom (F .Functor.F₀ x) (G .Functor.F₀ x))
  → Type _
is-natural-transformation {C} {D} F G η =
  ∀ x y (f : C .Hom x y) → η y D.∘ F .F₁ f ＝ G .F₁ f D.∘ η x
  where module D = Precategory D
        open Functor

module _ where
  open Precategory
  open Functor

  Const : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
        → Ob D → Functor C D
  Const {D} x .F₀ _ = x
  Const {D} x .F₁ _ = id D
  Const {D} x .F-id = refl
  Const {D} x .F-∘ _ _ = id-r D _ ⁻¹

  const-nt : {C : Precategory oᶜ hᶜ} {D : Precategory oᶜ hᵈ}
           → {x y : Ob D} → Hom D x y
           → Const {C = C} {D = D} x ⇒ Const {C = C} {D = D} y
  const-nt f ._⇒_.η _ = f
  const-nt {D} f ._⇒_.is-natural _ _ _ = id-r D _ ∙ id-l D _ ⁻¹

infixr 30 _∘ᶠ_
infix 20 _⇒_

module _ {C : Precategory oᶜ hᶜ}
         {D : Precategory oᶜ hᵈ}
         {F G : Functor C D} where
  private
    module F = Functor F
    module G = Functor G
    module D = Precategory D
    module C = Precategory C

  open Functor
  open _⇒_

  nat-pathᴾ : {F' G' : Functor C D}
            → (p : F ＝ F') (q : G ＝ G')
            → {a : F ⇒ G} {b : F' ⇒ G'}
            → (∀ x → ＜ a .η x ／ _ ＼ b .η x ＞)
            → ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
  nat-pathᴾ p q path i .η x = path x i
  nat-pathᴾ p q {a} {b} path i .is-natural x y f =
    is-prop→pathᴾ
      (λ i → is-prop-η $ is-set-β (D.Hom-set _ _)
        (path y i D.∘ Functor.F₁ (p i) f) (Functor.F₁ (q i) f D.∘ path x i))
      (a .is-natural x y f)
      (b .is-natural x y f) i

  nat-path : {a b : F ⇒ G}
           → ((x : _) → a .η x ＝ b .η x)
           → a ＝ b
  nat-path = nat-pathᴾ refl refl

  _ηₚ_ : ∀ {a b : F ⇒ G} → a ＝ b → ∀ x → a .η x ＝ b .η x
  p ηₚ x = ap (λ e → e .η x) p

  _ηᵈ_ : ∀ {F' G' : Functor C D} {p : F ＝ F'} {q : G ＝ G'}
       → {a : F ⇒ G} {b : F' ⇒ G'}
       →                      ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
       → ∀ x → ＜ a .η x ／ (λ i → D.Hom (p i .F₀ x) (q i .F₀ x)) ＼ b .η x ＞
  p ηᵈ x = apᴾ (λ i e → e .η x) p

  infixl 45 _ηₚ_

  instance
    Extensional-natural-transformation
      : ∀ {ℓr}
      → ⦃ sa : {x : ⌞ C ⌟} → Extensional (D .Hom (F $ x) (G $ x)) ℓr ⦄
      → Extensional (F ⇒ G) (oᶜ ⊔ ℓr)
    Extensional-natural-transformation ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f .η i) (g .η i)
    Extensional-natural-transformation ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x .η i)
    Extensional-natural-transformation ⦃ sa ⦄ .idsᵉ .to-path x = nat-path
      λ i → sa .idsᵉ .to-path (x i)
    Extensional-natural-transformation ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathᴾ
        (λ i → Π-is-of-hlevel 1
          λ _ → ≃→is-of-hlevel 1 (identity-system-gives-path (sa .idsᵉ)) (is-prop-η $ is-set-β (D .Hom-set _ _) _ _))
        _ _
