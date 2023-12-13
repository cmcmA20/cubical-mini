{-# OPTIONS --safe #-}
module Categories.Base where

open import Foundations.Base hiding (id ; _∘_)

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.Variadic

open import Structures.n-Type

record Precategory (o h : Level) : Type (ℓsuc (o ⊔ h)) where
  -- no-eta-equality
  -- ^ this sucks, gonna wait for agda issue #6721
  infixr 40 _∘_
  field
    Ob  : Type o
    Hom : Ob → Ob → Type h
    Hom-set : (x y : Ob) → is-set (Hom x y)
    id  : ∀ {x} → Hom x x
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    idl : ∀ {x y} (f : Hom x y) → id ∘ f ＝ f
    idr : ∀ {x y} (f : Hom x y) → f ∘ id ＝ f
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (h : Hom w x)
          → f ∘ (g ∘ h) ＝ (f ∘ g) ∘ h

private variable
  o h oᶜ hᶜ oᵈ hᵈ oᵉ hᵉ : Level

open Precategory

instance
  Underlying-precat : Underlying (Precategory o h)
  Underlying-precat {o} .Underlying.ℓ-underlying = o
  Underlying-precat .Underlying.⌞_⌟⁰ = Ob

infixl 60 _ᵒᵖ
_ᵒᵖ : Precategory o h → Precategory o h
(C ᵒᵖ) .Ob = Ob C
(C ᵒᵖ) .Hom x y = Hom C y x
(C ᵒᵖ) .Hom-set x y = Hom-set C y x
(C ᵒᵖ) .id = id C
(C ᵒᵖ) ._∘_ f g = C ._∘_ g f
(C ᵒᵖ) .idl x = C .idr x
(C ᵒᵖ) .idr x = C .idl x
(C ᵒᵖ) .assoc f g h i = assoc C h g f (~ i)

precat-double-dual : {C : Precategory oᶜ hᶜ} → C ᵒᵖ ᵒᵖ ＝ C
precat-double-dual = refl

Sets : (o : Level) → Precategory (ℓsuc o) o
Sets o .Ob = Set o
Sets _ .Hom A B = ⌞ A ⌟ → ⌞ B ⌟
Sets _ .Hom-set _ = hlevel!
Sets _ .id x = x
Sets _ ._∘_ f g x = f (g x)
Sets _ .idl _ = refl
Sets _ .idr _ = refl
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

functor-double-dual : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {F : Functor C D}
                    → Functor.op (Functor.op F) ＝ F
functor-double-dual {F} i .Functor.F₀ = F .Functor.F₀
functor-double-dual {F} i .Functor.F₁ = F .Functor.F₁
functor-double-dual {F} i .Functor.F-id = F .Functor.F-id
functor-double-dual {F} i .Functor.F-∘ = F .Functor.F-∘

_F∘_ : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {E : Precategory oᵉ hᵉ}
     → Functor D E → Functor C D → Functor C E
_F∘_ {C} {D} {E} F G = comps
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

{-# DISPLAY F∘.comps F G = F F∘ G #-}

Id : {C : Precategory oᶜ hᶜ} → Functor C C
Functor.F₀ Id x = x
Functor.F₁ Id f = f
Functor.F-id Id = refl
Functor.F-∘ Id _ _ = refl


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
  op .is-natural x y f = sym (is-natural y x f)

{-# INLINE NT #-}

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
  Const {D} x .F-∘ _ _ = sym (idr D _)

  const-nt : {C : Precategory oᶜ hᶜ} {D : Precategory oᶜ hᵈ}
           → {x y : Ob D} → Hom D x y
           → Const {C = C} {D = D} x ⇒ Const {C = C} {D = D} y
  const-nt f ._⇒_.η _ = f
  const-nt {D} f ._⇒_.is-natural _ _ _ = idr D _ ∙ sym (idl D _)

infixr 30 _F∘_
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

  nat-is-set : is-set (F ⇒ G)
  nat-is-set = iso→is-of-hlevel 2 eqv hlevel! where
    unquoteDecl eqv = declare-record-iso eqv (quote _⇒_)
    instance
      ds : ∀{x y} → H-Level 2 (D.Hom x y)
      ds = hlevel-basic-instance 2 $ D.Hom-set _ _

  nat-pathP : {F' G' : Functor C D}
            → (p : F ＝ F') (q : G ＝ G')
            → {a : F ⇒ G} {b : F' ⇒ G'}
            → (∀ x → ＜ a .η x ／ _ ＼ b .η x ＞)
            → PathP (λ i → p i ⇒ q i) a b
  nat-pathP p q path i .η x = path x i
  nat-pathP p q {a} {b} path i .is-natural x y f =
    is-prop→pathP
      (λ i → is-prop-η $ is-set-β (D.Hom-set _ _)
        (path y i D.∘ Functor.F₁ (p i) f) (Functor.F₁ (q i) f D.∘ path x i))
      (a .is-natural x y f)
      (b .is-natural x y f) i

  nat-path : {a b : F ⇒ G}
           → ((x : _) → a .η x ＝ b .η x)
           → a ＝ b
  nat-path = nat-pathP refl refl

  _ηₚ_ : ∀ {a b : F ⇒ G} → a ＝ b → ∀ x → a .η x ＝ b .η x
  p ηₚ x = ap (λ e → e .η x) p

  _ηᵈ_ : ∀ {F' G' : Functor C D} {p : F ＝ F'} {q : G ＝ G'}
       → {a : F ⇒ G} {b : F' ⇒ G'}
       →                      ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
       → ∀ x → ＜ a .η x ／ (λ i → D.Hom (p i .F₀ x) (q i .F₀ x)) ＼ b .η x ＞
  p ηᵈ x = apP (λ i e → e .η x) p

  infixl 45 _ηₚ_
