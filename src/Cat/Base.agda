{-# OPTIONS --safe --no-exact-split #-}
module Cat.Base where

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

    instance
      H-Level-Hom : ∀ {x y} {k} → H-Level (2 + k) (Hom x y)
      H-Level-Hom = hlevel-basic-instance 2 hom-set′

  instance
    Refl-Hom : Refl Hom
    Refl-Hom .refl = id

    Trans-Hom : Trans Hom
    Trans-Hom ._∙_ f g = g ∘ f

    HAssoc-Hom : HAssoc Hom
    HAssoc-Hom .∙-assoc f g h = assoc h g f ⁻¹

    HUnit-o-Hom : HUnit-o Hom
    HUnit-o-Hom .∙-id-o = id-r

    HUnit-i-Hom : HUnit-i Hom
    HUnit-i-Hom .∙-id-i = id-l

    ⇒-Hom : ⇒-notation Ob Ob (𝒰 h)
    ⇒-Hom ._⇒_ = Hom
    {-# INCOHERENT ⇒-Hom #-}

private variable
  o h ℓ o′ h′ ℓ′ o″ h″ ℓ″ oᶜ hᶜ oᵈ hᵈ oᵉ hᵉ : Level
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

  Dual-Cat : Has-unary-op (Precategory o ℓ)
  Dual-Cat .minv C .Ob = Ob C
  Dual-Cat .minv C .Hom x y = Hom C y x
  Dual-Cat .minv C .Hom-set x y = Hom-set C y x
  Dual-Cat .minv C .id = C .id
  Dual-Cat .minv C ._∘_ f g = C ._∘_ g f
  Dual-Cat .minv C .id-l = C .id-r
  Dual-Cat .minv C .id-r = C .id-l
  Dual-Cat .minv C .assoc f g h i = assoc C h g f (~ i)

  Invol-Dual-Cat : Invol (Precategory o ℓ)
  Invol-Dual-Cat .minv-invol _ = refl

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

unquoteDecl functor-iso = declare-record-iso functor-iso (quote Functor)

instance
  ⇒-Precat : ⇒-notation (Precategory o ℓ) (Precategory o′ ℓ′) (Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⇒-Precat ._⇒_ = Functor

  Dual-Functor : Dual {A = Precategory oᶜ hᶜ} {B = Precategory oᵈ hᵈ} Functor λ D C → Functor (C ᵒᵖ) (D ᵒᵖ)
  Dual-Functor ._ᵒᵖ F .Functor.F₀ = F .Functor.F₀
  Dual-Functor ._ᵒᵖ F .Functor.F₁ = F .Functor.F₁
  Dual-Functor ._ᵒᵖ F .Functor.F-id = F .Functor.F-id
  Dual-Functor ._ᵒᵖ F .Functor.F-∘ f g = F .Functor.F-∘ g f

  Dual-Functor⁻ : Dual {A = Precategory oᶜ hᶜ} {B = Precategory oᵈ hᵈ} (λ D C → Functor (C ᵒᵖ) (D ᵒᵖ)) Functor
  Dual-Functor⁻ ._ᵒᵖ F = Dual-Functor ._ᵒᵖ F
  {-# INCOHERENT Dual-Functor⁻ #-}

  Funlike-Functor₀
    : ∀ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
    → Funlike ur (Functor C D) ⌞ C ⌟ (λ _ → ⌞ D ⌟)
  Funlike-Functor₀  ._#_ = Functor.F₀

  Funlike-Functor₁
    : ∀ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
      {x y : ⌞ C ⌟}
    → Funlike ur (Functor C D) (Hom C x y) λ (F , _) → Hom D (F # x) (F # y)
  Funlike-Functor₁ ._#_ F = F .Functor.F₁

  GInvol-Dual-Functor : GInvol {A = Precategory oᶜ hᶜ} {B = Precategory oᵈ hᵈ} Functor (λ D′ C′ → Functor (C′ ᵒᵖ) (D′ ᵒᵖ))
  GInvol-Dual-Functor .invol F _ .Functor.F₀ = F .Functor.F₀
  GInvol-Dual-Functor .invol F _ .Functor.F₁ = F .Functor.F₁
  GInvol-Dual-Functor .invol F _ .Functor.F-id = F .Functor.F-id
  GInvol-Dual-Functor .invol F _ .Functor.F-∘ = F .Functor.F-∘

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
    F₀ x = F $ G $ x

    F₁ : {x y : C.Ob} → x ⇒ y → F₀ x ⇒ F₀ y
    F₁ f = F $ G $ f

    opaque
      F-id : {x : C.Ob} → F₁ (C.id {x}) ＝ E.id {F₀ x}
      F-id =
          F # (G # C.id)  ~⟨ ap$ F G.F-id ⟩
          F # D.id        ~⟨ F.F-id ⟩
          E.id            ∎

      F-∘ : {x y z : C.Ob} (f : y ⇒ z) (g : x ⇒ y)
          → F₁ (g ∙ f) ＝ F₁ g ∙ F₁ f
      F-∘ f g =
        F # (G # (g ∙ f))           ~⟨ ap$ F (G.F-∘ f g) ⟩
        F # (G # g ∙ G # f)         ~⟨ F.F-∘ (G.F₁ f) (G.F₁ g) ⟩
        F.F₁ (G # g) ∙ F # (G # f)  ∎

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

  Comp-Functor : Comp (Functor {oᶜ} {hᶜ}) (Functor {oᵈ} {hᵈ} {oᵉ} {hᵉ}) Functor
  Comp-Functor ._∙_ F G = G ∘ᶠ F

  GAssoc-Functor
    : GAssoc {A = Precategory o h} {B = Precategory o′ h′}
             {C = Precategory oᶜ hᶜ} {D = Precategory oᵈ hᵈ}
             Functor Functor Functor Functor Functor Functor
  GAssoc-Functor .∙-assoc F G H = Equiv.injective (≅→≃ functor-iso) (refl ,ₚ refl ,ₚ prop!)

  GUnit-o-Functor : GUnit-o {A = Precategory o ℓ} {B = Precategory o′ ℓ′} Functor Functor
  GUnit-o-Functor .∙-id-o F = Equiv.injective (≅→≃ functor-iso) (refl ,ₚ refl ,ₚ prop!)

  GUnit-i-Functor : GUnit-i {A = Precategory o ℓ} {B = Precategory o′ ℓ′} Functor Functor
  GUnit-i-Functor .∙-id-i F = Equiv.injective (≅→≃ functor-iso) (refl ,ₚ refl ,ₚ prop!)

  ≅-Cat : ≅-notation (Precategory o ℓ) (Precategory o′ ℓ′) (𝒰 (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ≅-Cat ._≅_ = Iso Functor Functor

-- basic properties of functors

is-full : C ⇒ D → Type _
is-full {C} {D} F =
    {x y : C.Ob} (g : F # x ⇒ F # y)
  → ∃[ f ꞉ x ⇒ y ] (F # f ＝ g)
    where
      module C = Precategory C
      module D = Precategory D

is-faithful : C ⇒ D → Type _
is-faithful {C} F = {x y : C.Ob} → Injective (Functor.F₁ F {x} {y})
  where module C = Precategory C

is-fully-faithful : C ⇒ D → Type _
is-fully-faithful {C} F = {x y : C.Ob} → is-equiv (Functor.F₁ F {x} {y})
  where module C = Precategory C


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
    η : (x : C.Ob) → F # x ⇒ G # x
    is-natural : (x y : C.Ob) (f : x ⇒ y)
               → F # f ∙ η y ＝ η x ∙ G # f

{-# INLINE NT #-}

unquoteDecl H-Level-NT = declare-record-hlevel 2 H-Level-NT (quote _=>_)
unquoteDecl NT-iso = declare-record-iso NT-iso (quote _=>_)

instance
  ⇒-nt : ⇒-notation (C ⇒ D) (C ⇒ D) _
  ⇒-nt ._⇒_ = _=>_

  Dual-nt
    : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
    → Dual {A = Functor C D} {B = Functor C D} _=>_ λ G F → G ᵒᵖ => F ᵒᵖ
  Dual-nt ._ᵒᵖ α ._=>_.η = α ._=>_.η
  Dual-nt ._ᵒᵖ α ._=>_.is-natural x y f = _=>_.is-natural α y x f ⁻¹

  Funlike-nt₀
    : {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {F G : C ⇒ D}
    → Funlike ur (F ⇒ G) ⌞ C ⌟ (λ (_ , x) → D .Precategory.Hom (F $ x) (G $ x))
  Funlike-nt₀ ._#_ = _=>_.η

  Refl-nt : Refl (_=>_ {C = C} {D = D})
  Refl-nt {D} .refl ._=>_.η _ = D .id
  Refl-nt {D} .refl {(F)} ._=>_.is-natural _ _ _ =
    D .id-l _ ∙ D .id-r _ ⁻¹

  Whisker-i-Functor-nt
    : {X : Precategory o h} {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
    → Whisker-i
        Functor Functor Functor (λ _ _ → ⊤) _ _
        X C D D
        (λ _ → _=>_)
        (λ _ → _=>_)
  Whisker-i-Functor-nt ._◁_ H α ._=>_.η x = α # (H # x)
  Whisker-i-Functor-nt ._◁_ H α ._=>_.is-natural x y f =
    α ._=>_.is-natural (H # x) (H # y) (H # f)

  Whisker-o-Functor-nt
    : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} {X : Precategory o h}
    → Whisker-o
        Functor Functor (λ _ _ → ⊤) Functor _ _
        C C D X
        (λ _ → _=>_)
        (λ _ → _=>_)
  Whisker-o-Functor-nt ._▷_ α K ._=>_.η x = K # (α # x)
  Whisker-o-Functor-nt ._▷_ α K ._=>_.is-natural x y f
    = Functor.F-∘ K (α # y) _ ⁻¹
    ∙ ap$ K (α ._=>_.is-natural x y f)
    ∙ Functor.F-∘ K _ (α # x)

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
      F # f ∙ β # y ∙ α # y      ~⟨ D.assoc _ _ _ ⟨
      (F # f ∙ β # y) ∙ α # y    ~⟨ β ._=>_.is-natural x y f ▷ α # y ⟩
      (β # x ∙ G # f) ∙ α # y    ~⟨ D.assoc _ _ _ ⟩
      β # x ∙ G # f ∙ α # y      ~⟨ β # x ◁ α ._=>_.is-natural x y f ⟩
      β # x ∙ α # x ∙ H # f      ~⟨ D.assoc _ _ _ ⟨
      (β # x ∙ α # x) ∙ H # f    ∎


{-# DISPLAY =>∘.comps F G = F ∘ⁿᵗ G #-}

instance
  Comp-nt : Comp (_=>_ {C = C} {D = D}) _=>_ _=>_
  Comp-nt ._∙_ α β = β ∘ⁿᵗ α


is-natural-transformation
  : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
  → (F G : C ⇒ D)
  → (η : (x : C .Ob) → D .Hom (F $ x) (G $ x))
  → Type _
is-natural-transformation {C} {D} F G η =
  ∀ x y (f : x ⇒ y) → F # f ∙ η y ＝ η x ∙ G # f
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
         {D : Precategory oᵈ hᵈ}
         {F G : C ⇒ D} where
  private
    module F = Functor F
    module G = Functor G
    module D = Precategory D
    module C = Precategory C

  open Functor
  open _=>_

  nt-pathᴾ : {F′ G′ : Functor C D}
           → (p : F ＝ F′) (q : G ＝ G′)
           → {a : F ⇒ G} {b : F′ ⇒ G′}
           → (∀ x → ＜ a $ x ／ _ ＼ b $ x ＞)
           → ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
  nt-pathᴾ p q path i .η x = path x i
  nt-pathᴾ p q {a} {b} path i .is-natural x y f =
    is-prop→pathᴾ
      (λ i → (D.Hom-set _ _)
        (path y i D.∘ Functor.F₁ (p i) f) (Functor.F₁ (q i) f D.∘ path x i))
      (a .is-natural x y f)
      (b .is-natural x y f) i

  _ηᵈ_ : {F′ G′ : C ⇒ D} {p : F ＝ F′} {q : G ＝ G′}
       → {a : F ⇒ G} {b : F′ ⇒ G′}
       →                      ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
       → (x : C.Ob) → ＜ a $ x ／ (λ i → D.Hom (p i $ x) (q i $ x)) ＼ b $ x ＞
  p ηᵈ x = apᴾ (λ i e → e $ x) p

  instance
    Funlike-nt-homotopy
      : {α β : F ⇒ G}
      → Funlike ur (α ＝ β) C.Ob λ (p , x) → α # x ＝ β # x
    Funlike-nt-homotopy ._#_ p x = ap (_$ x) p

    Extensional-nt
      : ∀ {ℓr}
      → ⦃ sa : {x : ⌞ C ⌟} → Extensional (D .Hom (F $ x) (G $ x)) ℓr ⦄
      → Extensional (F ⇒ G) (oᶜ ⊔ ℓr)
    Extensional-nt ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f $ i) (g $ i)
    Extensional-nt ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x $ i)
    Extensional-nt ⦃ sa ⦄ .idsᵉ .to-path x = nt-pathᴾ refl refl
      λ i → sa .idsᵉ .to-path (x i)
    Extensional-nt ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathᴾ
        (λ i → Π-is-of-hlevel 1
          λ _ → ≃→is-of-hlevel 1 (identity-system-gives-path (sa .idsᵉ)) (D .Hom-set _ _ _ _))
        _ _

module _ {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} where
  private
    module C = Precategory C
    module D = Precategory D

  instance
    GAssoc-nt
      : GAssoc {A = Functor C D} _=>_ _=>_ _=>_ _=>_ _=>_ _=>_
    GAssoc-nt .∙-assoc α β γ = ext λ c →
      D.assoc (γ # c) (β # c) (α # c) ⁻¹

    GUnit-o-nt : GUnit-o {A = Functor C D} _=>_ _=>_
    GUnit-o-nt .∙-id-o α = ext λ c → D.id-r (α # c)

    GUnit-i-nt : GUnit-i {A = Functor C D} _=>_ _=>_
    GUnit-i-nt .∙-id-i α = ext λ c → D.id-l (α # c)

    ≅-Functor : ≅-notation (Functor C D) (Functor C D) (𝒰 (oᶜ ⊔ hᶜ ⊔ hᵈ))
    ≅-Functor ._≅_ = Iso _=>_ _=>_

    Funlike-nt₁
      : {F G : C ⇒ D} {x y : ⌞ C ⌟}
      → Funlike ur (F ⇒ G) (C .Precategory.Hom x y) λ (α , f) → F # f ∙ α # y ＝ α # x ∙ G # f
    Funlike-nt₁ ._#_ α = _=>_.is-natural α _ _

    ⊣-Functor : ⊣-notation (Functor C D) (Functor D C) (𝒰 (oᶜ ⊔ hᶜ ⊔ oᵈ ⊔ hᵈ))
    ⊣-Functor ._⊣_ L R = Adjoint Functor Functor Functor Functor C C.Hom D D.Hom L R _=>_ _=>_
