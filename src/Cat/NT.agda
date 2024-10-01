{-# OPTIONS --safe --no-exact-split #-}
module Cat.NT where

open import Meta.Prelude
  hiding (id ; _∘_)
open import Meta.Extensionality
open import Meta.Record

open import Structures.n-Type

open import Cat.Base
open import Cat.Functor.Base

open import Data.Unit.Base

private variable
  o h o′ h′ oᶜ hᶜ oᵈ hᵈ oᵉ hᵉ : Level
  C : Precategory oᶜ hᵈ
  D : Precategory oᵈ hᵈ
  n : HLevel

record _=>_ {C : Precategory oᶜ hᶜ}
            {D : Precategory oᵈ hᵈ}
            (F G : Functor C D)
      : Type (oᶜ ⊔ hᶜ ⊔ hᵈ)
  where
  no-eta-equality
  constructor make-nt
  private
    module C = Precategory C
    module D = Precategory D

  field
    η : (x : C.Ob) → F # x ⇒ G # x
    is-natural : (x y : C.Ob) (f : x ⇒ y)
               → F # f ∙ η y ＝ η x ∙ G # f

{-# INLINE make-nt #-}

unquoteDecl NT-iso = declare-record-iso NT-iso (quote _=>_)

open Precategory

instance opaque
  H-Level-NT
    : {F G : C ⇒ D} ⦃ _ : n ≥ʰ 1 ⦄
    → ⦃ hl : ∀ {x y} → H-Level n (D .Hom x y) ⦄ → H-Level n (F => G)
  H-Level-NT {D} ⦃ s≤ʰs _ ⦄ ⦃ hl ⦄ .H-Level.has-of-hlevel = ≅→is-of-hlevel _ NT-iso
    $ Σ-is-of-hlevel _ (hlevel _) λ z → Π³-is-of-hlevel _ λ x y f
    → path-is-of-hlevel _ (is-of-hlevel-suc (suc _) (hlevel _)) _ _

instance
  ⇒-nt : ⇒-notation (C ⇒ D) (C ⇒ D) _
  ⇒-nt .⇒-notation.Constraint _ _ = ⊤ₜ
  ⇒-nt ._⇒_ α β = α => β

  Dual-nt
    : {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ}
    → Dual {A = Functor C D} {B = Functor C D} _=>_ λ G F → G ᵒᵖ => F ᵒᵖ
  Dual-nt ._ᵒᵖ α ._=>_.η = α ._=>_.η
  Dual-nt ._ᵒᵖ α ._=>_.is-natural x y f = _=>_.is-natural α y x f ⁻¹

  Funlike-nt₀
    : {C : Precategory o h} {D : Precategory o′ h′} {F G : C ⇒ D}
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
      F # f ∙ β # y ∙ α # y      ~⟨ D.assoc _ _ _ ⟩
      (F # f ∙ β # y) ∙ α # y    ~⟨ β ._=>_.is-natural x y f ▷ α # y ⟩
      (β # x ∙ G # f) ∙ α # y    ~⟨ D.assoc _ _ _ ⟨
      β # x ∙ G # f ∙ α # y      ~⟨ β # x ◁ α ._=>_.is-natural x y f ⟩
      β # x ∙ α # x ∙ H # f      ~⟨ D.assoc _ _ _ ⟩
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

const-nt : {x y : Ob D} → Hom D x y
         → Const {D = D} {C = C} x ⇒ Const y
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
           → (r : ∀ x → ＜ a $ x ／ _ ＼ b $ x ＞)
           → (s : ∀ x y f → ＜ a .is-natural x y f ／ (λ i → p i # f ∙ r y i ＝ r x i ∙ q i # f) ＼ b .is-natural x y f ＞)
           → ＜ a ／ (λ i → p i ⇒ q i) ＼ b ＞
  nt-pathᴾ p q r s i .η x = r x i
  nt-pathᴾ p q {a} {b} r s i .is-natural x y f = s x y f i

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
        ⦃ hl : ∀ {x y} → H-Level 2 (D .Hom x y) ⦄
      → Extensional (F ⇒ G) (oᶜ ⊔ ℓr)
    Extensional-nt ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f $ i) (g $ i)
    Extensional-nt ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x $ i)
    Extensional-nt ⦃ sa ⦄ .idsᵉ .to-path x = nt-pathᴾ refl refl
      (λ i → sa .idsᵉ .to-path (x i)) λ _ _ _ → prop!
    Extensional-nt ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathᴾ
        (λ i → Π-is-of-hlevel 1
          λ _ → ≃→is-of-hlevel 1 (identity-system-gives-path (sa .idsᵉ)) (hlevel 1))
        _ _

module _ {C : Precategory oᶜ hᶜ} {D : Precategory oᵈ hᵈ} where
  private
    module C = Precategory C
    module D = Precategory D

  instance
    ≅-Functor : ≅-notation (Functor C D) (Functor C D) (𝒰 (oᶜ ⊔ hᶜ ⊔ hᵈ))
    ≅-Functor ._≅_ = Iso _=>_ _=>_

    ⊣-Functor : ⊣-notation (Functor C D) (Functor D C) (𝒰 (oᶜ ⊔ hᶜ ⊔ oᵈ ⊔ hᵈ))
    ⊣-Functor ._⊣_ L R = Adjoint Functor Functor Functor Functor C C.Hom D D.Hom L R _=>_ _=>_

    Funlike-nt₁
      : {F G : C ⇒ D} {x y : ⌞ C ⌟}
      → Funlike ur (F ⇒ G) (C .Precategory.Hom x y) λ (α , f) → F # f ∙ α # y ＝ α # x ∙ G # f
    Funlike-nt₁ ._#_ α = _=>_.is-natural α _ _

  module _ ⦃ hl : ∀ {x y} → H-Level 2 (D .Hom x y) ⦄ where instance
    GAssoc-nt
      : GAssoc {A = Functor C D} _=>_ _=>_ _=>_ _=>_ _=>_ _=>_
    GAssoc-nt .∙-assoc α β γ = ext λ c → D.assoc (α # c) (β # c) (γ # c)

    GUnit-o-nt : GUnit-o {A = Functor C D} _=>_ _=>_
    GUnit-o-nt .∙-id-o α = ext λ c → D.id-r (α # c)

    GUnit-i-nt : GUnit-i {A = Functor C D} _=>_ _=>_
    GUnit-i-nt .∙-id-i α = ext λ c → D.id-l (α # c)


Cat[_,_]
  : (C : Precategory o h) (D : Precategory o′ h′)
    ⦃ hl : ∀ {x y} → H-Level 2 (D .Hom x y) ⦄
  → Precategory (o ⊔ h ⊔ o′ ⊔ h′) (o ⊔ h ⊔ h′)
Cat[ C , D ] .Ob = C ⇒ D
Cat[ C , D ] .Hom x y = x ⇒ y
Cat[ C , D ] .id = refl
Cat[ C , D ] ._∘_ = flip _∙_
Cat[ C , D ] .id-l = ∙-id-i
Cat[ C , D ] .id-r = ∙-id-o
Cat[ C , D ] .assoc = ∙-assoc

instance
  ⇒-Precat-exp
    : ⇒-notation (Precategory o h) (Precategory o′ h′)
        (Precategory (o ⊔ h ⊔ o′ ⊔ h′) (o ⊔ h ⊔ h′))
  ⇒-Precat-exp .⇒-notation.Constraint _ D = ∀ {x y} → H-Level 2 (D .Hom x y)
  ⇒-Precat-exp ._⇒_ C D = Cat[ C , D ]

PSh : ∀ κ {o ℓ} → Precategory o ℓ → Precategory (o ⊔ ℓ ⊔ ℓsuc κ) (o ⊔ ℓ ⊔ κ)
PSh κ C = C ᵒᵖ ⇒ Sets κ
