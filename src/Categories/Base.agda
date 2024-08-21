{-# OPTIONS --safe --no-exact-split #-}
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
open import Data.Empty.Base
open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Term
open import Data.Truncation.Propositional.Base
open import Data.Unit.Base

open import Functions.Embedding using (Injective)

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
           → ＜ f .snd .snd ／ (λ i → Hom (p i) (q i)) ＼ g .snd .snd ＞
           → f ＝ g
  Mor-path p q r i = p i , q i , r i

  opaque
    hom-set′ : ∀ {x y} → is-set (Hom x y)
    hom-set′ = Hom-set _ _

  instance opaque
    H-Level-Hom : ∀ {x y} {k} → H-Level (2 + k) (Hom x y)
    H-Level-Hom = hlevel-basic-instance 2 hom-set′

  instance
    Refl-Hom : Refl Hom
    Refl-Hom .refl = id

    Trans-Hom : Transitive Hom
    Trans-Hom ._∙_ f g = g ∘ f

    ⇒-Hom : ⇒-notation Ob Ob (𝒰 h)
    ⇒-Hom ._⇒_ = Hom
    {-# INCOHERENT ⇒-Hom #-}

private variable
  o h ℓ o′ h′ ℓ′ oᶜ hᶜ oᵈ hᵈ oᵉ hᵉ : Level
  C : Precategory oᶜ hᵈ
  D : Precategory oᵈ hᵈ

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
Sets _ .Hom A B = ⌞ A ⇒ B ⌟
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
    F₁ : ∀ {x y : C.Ob} → x ⇒ y → F₀ x ⇒ F₀ y
    F-id : ∀ {x} → F₁ (C.id {x}) ＝ D.id
    F-∘ : ∀ {x y z : C.Ob} (f : y ⇒ z) (g : x ⇒ y)
        → F₁ (g ∙ f) ＝ F₁ g ∙ F₁ f

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

  ⇒-Precat : ⇒-notation (Precategory o ℓ) (Precategory o′ ℓ′) (Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⇒-Precat ._⇒_ = Functor

functor-double-dual : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {F : Functor C D}
                    → Functor.op (Functor.op F) ＝ F
functor-double-dual {F} i .Functor.F₀ = F .Functor.F₀
functor-double-dual {F} i .Functor.F₁ = F .Functor.F₁
functor-double-dual {F} i .Functor.F-id = F .Functor.F-id
functor-double-dual {F} i .Functor.F-∘ = F .Functor.F-∘

_∘ᶠ_ : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {E : Precategory oᵉ hᵉ}
     → D ⇒ E → C ⇒ D → C ⇒ E
_∘ᶠ_ {C} {D} {E} F G = comps
  module F∘ where
    module C = Precategory C
    module D = Precategory D
    module E = Precategory E

    module F = Functor F
    module G = Functor G

    F₀ : C.Ob → E.Ob
    F₀ x = F.₀ (G.₀ x)

    F₁ : {x y : C.Ob} → x ⇒ y → F₀ x ⇒ F₀ y
    F₁ f = F.₁ (G.₁ f)

    opaque
      F-id : {x : C.Ob} → F₁ (C.id {x}) ＝ E.id {F₀ x}
      F-id =
          F.₁ (G.₁ C.id)  ~⟨ ap F.₁ G.F-id ⟩
          F.₁ D.id        ~⟨ F.F-id ⟩
          E.id            ∎

      F-∘ : {x y z : C.Ob} (f : y ⇒ z) (g : x ⇒ y)
          → F₁ (g ∙ f) ＝ F₁ g ∙ F₁ f
      F-∘ f g =
          F.₁ (G.₁ (f C.∘ g))    ~⟨ ap F.₁ (G.F-∘ f g) ⟩
          F.₁ (G.₁ f D.∘ G.₁ g)  ~⟨ F.F-∘ _ _ ⟩
          F₁ f E.∘ F₁ g          ∎

    comps : Functor _ _
    comps .Functor.F₀ = F₀
    comps .Functor.F₁ = F₁
    comps .Functor.F-id = F-id
    comps .Functor.F-∘ = F-∘

{-# DISPLAY F∘.comps F G = F ∘ᶠ G #-}

Id : {C : Precategory oᶜ hᶜ} → C ⇒ C
Functor.F₀ Id = refl
Functor.F₁ Id = refl
Functor.F-id Id = refl
Functor.F-∘ Id _ _ = refl

instance
  Refl-Functor : Refl (Functor {oᶜ} {hᶜ})
  Refl-Functor .refl = Id

  Trans-Functor : Trans (Functor {oᶜ} {hᶜ}) (Functor {oᵈ} {hᵈ} {oᵉ} {hᵉ}) Functor
  Trans-Functor ._∙_ F G = G ∘ᶠ F


-- basic properties of functors

is-full : C ⇒ D → Type _
is-full {C} {D} F =
    {x y : C.Ob} (g : F.₀ x ⇒ F.₀ y)
  → ∃[ f ꞉ x ⇒ y ] (F.₁ f ＝ g)
    where
      module C = Precategory C
      module D = Precategory D
      module F = Functor F

is-faithful : C ⇒ D → Type _
is-faithful {C} F = {x y : C.Ob} → Injective (F.₁ {x} {y})
  where
    module C = Precategory C
    module F = Functor F

is-fully-faithful : C ⇒ D → Type _
is-fully-faithful {C} F = {x y : C.Ob} → is-equiv (F.₁ {x} {y})
  where
    module C = Precategory C
    module F = Functor F


-- Natural transformations

record _=>_ {C : Precategory oᶜ hᶜ}
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
    η : (x : C.Ob) → F.₀ x ⇒ G.₀ x
    is-natural : (x y : C.Ob) (f : x ⇒ y)
               → F.₁ f ∙ η y ＝ η x ∙ G.₁ f

  op : Functor.op G => Functor.op F
  op .η = η
  op .is-natural x y f = is-natural y x f ⁻¹

{-# INLINE NT #-}

unquoteDecl H-Level-NT = declare-record-hlevel 2 H-Level-NT (quote _=>_)

instance
  ⇒-natural-transformation : ⇒-notation (C ⇒ D) (C ⇒ D) _
  ⇒-natural-transformation ._⇒_ = _=>_

  Funlike-natural-transformation
    : {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {F G : C ⇒ D}
    → Funlike ur (F ⇒ G) ⌞ C ⌟ (λ x → D .Precategory.Hom (F $ x) (G $ x))
  Funlike-natural-transformation ._#_ = _=>_.η

  Refl-natural-transformation : Refl (_=>_ {C = C} {D = D})
  Refl-natural-transformation {D} .refl ._=>_.η _ = D .id
  Refl-natural-transformation {D} .refl {(F)} ._=>_.is-natural _ _ _ =
    D .id-l _ ∙ D .id-r _ ⁻¹

_∘ⁿᵗ_ : {F G H : Functor C D} → G ⇒ H → F ⇒ G → F ⇒ H
_∘ⁿᵗ_ {C} {D} {F} {G} {H} α β = comps
  module =>∘ where
    module D = Precategory D

    module F = Functor F
    module G = Functor G
    module H = Functor H

    comps : F => H
    comps ._=>_.η x = β # x ∙ α # x
    comps ._=>_.is-natural x y f =
      (α # y D.∘ β # y) D.∘ F.₁ f  ~⟨ D.assoc _ _ _ ⟨
      α # y D.∘ β # y D.∘ F.₁ f    ~⟨ ap (α # y D.∘_) (β ._=>_.is-natural x y f) ⟩
      α # y D.∘ G.₁ f D.∘ β # x    ~⟨ D.assoc _ _ _ ⟩
      (α # y D.∘ G.₁ f) D.∘ β # x  ~⟨ ap (D._∘ β # x) (α ._=>_.is-natural x y f) ⟩
      (H.₁ f D.∘ α # x) D.∘ β # x  ~⟨ D.assoc _ _ _ ⟨
      H.₁ f D.∘ α # x D.∘ β # x    ∎

{-# DISPLAY =>∘.comps F G = F ∘ⁿᵗ G #-}

instance
  Trans-natural-transformation : Trans (_=>_ {C = C} {D = D}) _=>_ _=>_
  Trans-natural-transformation ._∙_ α β = β ∘ⁿᵗ α

is-natural-transformation
  : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
  → (F G : C ⇒ D)
  → (η : (x : C .Ob) → D .Hom (F $ x) (G $ x))
  → Type _
is-natural-transformation {C} {D} F G η =
  ∀ x y (f : x ⇒ y) → F.₁ f ∙ η y ＝ η x ∙ G.₁ f
  where module C = Precategory C
        module D = Precategory D
        module F = Functor F
        module G = Functor G

module _ where
  open Precategory
  open Functor

  Const : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
        → Ob D → C ⇒ D
  Const {D} x .F₀ _ = x
  Const {D} x .F₁ _ = id D
  Const {D} x .F-id = refl
  Const {D} x .F-∘ _ _ = id-r D _ ⁻¹

  const-nt : {C : Precategory oᶜ hᶜ} {D : Precategory oᶜ hᵈ}
           → {x y : Ob D} → Hom D x y
           → Const {C = C} {D = D} x ⇒ Const y
  const-nt f ._=>_.η _ = f
  const-nt {D} f ._=>_.is-natural _ _ _ = D .id-r _ ∙ D .id-l _ ⁻¹


module _ {C : Precategory oᶜ hᶜ}
         {D : Precategory oᶜ hᵈ}
         {F G : C ⇒ D} where
  private
    module F = Functor F
    module G = Functor G
    module D = Precategory D
    module C = Precategory C

  open Functor
  open _=>_

  nat-pathᴾ : {F' G' : Functor C D}
            → (p : F ＝ F') (q : G ＝ G')
            → {a : F ⇒ G} {b : F' ⇒ G'}
            → (∀ x → ＜ a $ x ／ _ ＼ b $ x ＞)
            → ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
  nat-pathᴾ p q path i .η x = path x i
  nat-pathᴾ p q {a} {b} path i .is-natural x y f =
    is-prop→pathᴾ
      (λ i → (D.Hom-set _ _)
        (path y i D.∘ Functor.F₁ (p i) f) (Functor.F₁ (q i) f D.∘ path x i))
      (a .is-natural x y f)
      (b .is-natural x y f) i

  nat-path : {a b : F ⇒ G}
           → ((x : _) → a # x ＝ b # x)
           → a ＝ b
  nat-path = nat-pathᴾ refl refl

  _ηₚ_ : ∀ {a b : F ⇒ G} → a ＝ b → (x : C.Ob) → a # x ＝ b # x
  p ηₚ x = ap (_$ x) p

  _ηᵈ_ : {F' G' : C ⇒ D} {p : F ＝ F'} {q : G ＝ G'}
       → {a : F ⇒ G} {b : F' ⇒ G'}
       →                      ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
       → (x : C.Ob) → ＜ a $ x ／ (λ i → D.Hom (p i $ x) (q i $ x)) ＼ b $ x ＞
  p ηᵈ x = apᴾ (λ i e → e $ x) p

  infixl 45 _ηₚ_

  instance
    Extensional-natural-transformation
      : ∀ {ℓr}
      → ⦃ sa : {x : ⌞ C ⌟} → Extensional (D .Hom (F $ x) (G $ x)) ℓr ⦄
      → Extensional (F ⇒ G) (oᶜ ⊔ ℓr)
    Extensional-natural-transformation ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f $ i) (g $ i)
    Extensional-natural-transformation ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x $ i)
    Extensional-natural-transformation ⦃ sa ⦄ .idsᵉ .to-path x = nat-path
      λ i → sa .idsᵉ .to-path (x i)
    Extensional-natural-transformation ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathᴾ
        (λ i → Π-is-of-hlevel 1
          λ _ → ≃→is-of-hlevel 1 (identity-system-gives-path (sa .idsᵉ)) (D .Hom-set _ _ _ _))
        _ _

instance
  ⊥-Cat : ⊥-notation (Precategory o ℓ)
  ⊥-Cat .⊥ .Ob = ⊥
  ⊥-Cat .⊥ .Hom _ _ = ⊥

  ⊤-Cat : ⊤-notation (Precategory o ℓ)
  ⊤-Cat .⊤ .Ob = ⊤
  ⊤-Cat .⊤ .Hom _ _ = ⊤
  ⊤-Cat .⊤ .Hom-set _ _ = hlevel 2
  ⊤-Cat .⊤ .id = _
  ⊤-Cat .⊤ ._∘_ _ _ = _
  ⊤-Cat .⊤ .id-l _ = refl
  ⊤-Cat .⊤ .id-r _ = refl
  ⊤-Cat .⊤ .assoc _ _ _ = refl
