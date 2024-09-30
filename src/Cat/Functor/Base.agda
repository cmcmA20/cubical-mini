{-# OPTIONS --safe --no-exact-split #-}
module Cat.Functor.Base where

open import Meta.Prelude
  hiding (id ; _∘_)
open import Meta.Deriving.HLevel
open import Meta.Record

open import Structures.n-Type

open import Cat.Base

open import Data.Truncation.Propositional.Base

private variable
  o h o′ h′ oᶜ hᶜ oᵈ hᵈ oᵉ hᵉ : Level
  C : Precategory oᶜ hᵈ
  D : Precategory oᵈ hᵈ

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
  ⇒-Precat : ⇒-notation (Precategory o h) (Precategory o′ h′) (Type (o ⊔ h ⊔ o′ ⊔ h′))
  ⇒-Precat .⇒-notation.Constraint _ _ = ⊤ₜ
  ⇒-Precat ._⇒_ C D = Functor C D

  Dual-Functor : Dual {A = Precategory oᶜ hᶜ} {B = Precategory oᵈ hᵈ} Functor λ D C → Functor (C ᵒᵖ) (D ᵒᵖ)
  Dual-Functor ._ᵒᵖ F .Functor.F₀ = F .Functor.F₀
  Dual-Functor ._ᵒᵖ F .Functor.F₁ = F .Functor.F₁
  Dual-Functor ._ᵒᵖ F .Functor.F-id = F .Functor.F-id
  Dual-Functor ._ᵒᵖ F .Functor.F-∘ f g = F .Functor.F-∘ g f

  Dual-Functor⁻ : Dual {A = Precategory oᶜ hᶜ} {B = Precategory oᵈ hᵈ} (λ D C → Functor (C ᵒᵖ) (D ᵒᵖ)) Functor
  Dual-Functor⁻ ._ᵒᵖ F = Dual-Functor ._ᵒᵖ F
  {-# INCOHERENT Dual-Functor⁻ #-}

  Funlike-Functor₀ : Funlike ur (Functor C D) ⌞ C ⌟ (λ _ → ⌞ D ⌟)
  Funlike-Functor₀  ._#_ = Functor.F₀

  Funlike-Functor₁
    : {x y : ⌞ C ⌟}
    → Funlike ur (Functor C D) (Precategory.Hom C x y) λ (F , _) → Precategory.Hom D (F # x) (F # y)
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

open Functor

Id : C ⇒ C
Id .F₀ = refl
Id .F₁ = refl
Id .F-id = refl
Id .F-∘ _ _ = refl

Const : ⌞ D ⌟ → C ⇒ D
Const {D} x .F₀ _ = x
Const {D} x .F₁ _ = Precategory.id D
Const {D} x .F-id = refl
Const {D} x .F-∘ _ _ = Precategory.id-l D _ ⁻¹

instance
  Refl-Functor : Refl (Functor {oᶜ} {hᶜ})
  Refl-Functor .refl = Id

  Comp-Functor : Comp (Functor {oᶜ} {hᶜ}) (Functor {oᵈ} {hᵈ} {oᵉ} {hᵉ}) Functor
  Comp-Functor ._∙_ F G = G ∘ᶠ F

  ≅-Cat : ≅-notation (Precategory o h) (Precategory o′ h′) (𝒰 (o ⊔ h ⊔ o′ ⊔ h′))
  ≅-Cat ._≅_ = Iso Functor Functor

  -- XXX FIXME
  -- GAssoc-Functor
  --   : GAssoc {A = Precategory o h} {B = Precategory o′ h′}
  --            {C = Precategory oᶜ hᶜ} {D = Precategory oᵈ hᵈ}
  --            Functor Functor Functor Functor Functor Functor
  -- GAssoc-Functor .∙-assoc F G H = Equiv.injective (≅→≃ functor-iso) (refl ,ₚ refl ,ₚ prop!)

  -- GUnit-o-Functor : GUnit-o {A = Precategory o h} {B = Precategory o′ h′} Functor Functor
  -- GUnit-o-Functor .∙-id-o F = Equiv.injective (≅→≃ functor-iso) (refl ,ₚ refl ,ₚ prop!)

  -- GUnit-i-Functor : GUnit-i {A = Precategory o h} {B = Precategory o′ h′} Functor Functor
  -- GUnit-i-Functor .∙-id-i F = Equiv.injective (≅→≃ functor-iso) (refl ,ₚ refl ,ₚ prop!)
