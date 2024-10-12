{-# OPTIONS --safe #-}
module Foundations.Isomorphism where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Path.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  f : A → B

open Iso

Retractₜ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
Retractₜ = Retract Fun

Isoₜ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
Isoₜ = Iso Fun Fun

instance
  ≅-Fun : ≅-notation (𝒰 ℓ) (𝒰 ℓ′) (𝒰 (ℓ ⊔ ℓ′))
  ≅-Fun ._≅_ = Isoₜ

quasi-inverseᴱ : (f : A → B) → Type _
quasi-inverseᴱ {A} {B} f = Σ[ inv ꞉ (B → A) ]
  ( Erased (inv section-of f)
  × Erased (inv retraction-of f) )

Isoᴱ : Type ℓ → Type ℓ′ → Type _
Isoᴱ A B = Σ[ f ꞉ (A → B) ] quasi-inverseᴱ f

is-equivᴱ→qinvᴱ : is-equivᴱ f → quasi-inverseᴱ f
is-equivᴱ→qinvᴱ {f} eqv = is-equivᴱ→inverse eqv
                        , erase (fun-ext λ y → eqv y .fst .snd .erased)
                        , erase (fun-ext λ x → ap fst $ eqv (f x) .snd .erased (x , erase refl))

open quasi-inverse

qinv→qinvᴱ : {f : A → B} → quasi-inverse f → quasi-inverseᴱ f
qinv→qinvᴱ fi = fi .inv , erase (fi .inv-o) , erase (fi .inv-i)

id-qinvₜ : quasi-inverse (id {A = A})
id-qinvₜ .inv = id
id-qinvₜ .inverses .Inverses.inv-o = refl
id-qinvₜ .inverses .Inverses.inv-i = refl

qinv-compₜ : {f : A → B} {g : B → C} → quasi-inverse f → quasi-inverse g → quasi-inverse (f ∙ g)
qinv-compₜ fi gi .inv = gi .inv ∙ fi .inv
qinv-compₜ {f} {g} fi gi .inverses .Inverses.inv-o =
  (gi .inv ◁ fi .inv-o ▷ g) ∙ gi .inv-o
qinv-compₜ {f} {g} fi gi .inverses .Inverses.inv-i =
  (f ◁ gi .inv-i ▷ fi .inv) ∙ fi .inv-i

private
  retract-comp-helper
    : {ℓᵃ ℓᵇ ℓᶜ ℓᵇ̇ ℓᶜ̇ ℓf ℓf⁻ ℓg ℓg⁻ ℓfg ℓg⁻f⁻ : Level}
      {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
      {B∙ : B → B → 𝒰 ℓᵇ̇} {C∙ : C → C → 𝒰 ℓᶜ̇}
      ⦃ _ : Refl B∙ ⦄      ⦃ _ : Refl C∙ ⦄
      {F   : A → B → 𝒰 ℓf}  {F⁻    : B → A → 𝒰 ℓf⁻}
      {G   : B → C → 𝒰 ℓg}  {G⁻    : C → B → 𝒰 ℓg⁻}
      {F∙G : A → C → 𝒰 ℓfg} {G⁻∙F⁻ : C → A → 𝒰 ℓg⁻f⁻}
      ⦃ _ : Comp F⁻ F  B∙ ⦄ ⦃ _ : Comp G⁻ G  C∙ ⦄
      ⦃ _ : Comp F G  F∙G ⦄ ⦃ _ : Comp G⁻ F⁻ G⁻∙F⁻ ⦄ ⦃ _ : Comp G⁻∙F⁻ F∙G  C∙ ⦄
      ⦃ _ : Comp B∙ G  G ⦄ ⦃ _ : Comp F⁻ F∙G  G ⦄
      ⦃ _ : GAssoc F⁻ F  G  B∙  F∙G  G ⦄ ⦃ _ : GAssoc G⁻ F⁻ F∙G  G⁻∙F⁻ G  C∙  ⦄
      ⦃ _ : GUnit-o B∙ G  ⦄
      {a : A} {b : B} {c : C}
      (x : G⁻ c b) (y : F⁻ b a) (z : F a b) (w : G b c)
      (p : y ∙ z ＝ refl) (q : x ∙ w ＝ refl)
    → (x ∙ y) ∙ (z ∙ w) ＝ refl
  retract-comp-helper x y z w p q =
      (x ∙ y) ∙ (z ∙ w)  ~⟨ ∙-assoc x y (z ∙ w) ⟨
      x ∙ (y ∙ z ∙ w)    ~⟨ x ◁ ∙-assoc y z w ⟩
      x ∙ (y ∙ z) ∙ w    ~⟨ x ◁ p ▷ w ⟩
      x ∙ refl ∙ w       ~⟨ x ◁ ∙-id-o w ⟩
      x ∙ w              ~⟨ q ⟩
      _                  ∎


instance
  Comp-Retract
    : {ℓᵃ ℓᵇ ℓᶜ ℓᵃ̇ ℓᵇ̇ ℓf ℓf⁻ ℓg ℓg⁻ ℓfg ℓg⁻f⁻ : Level}
      {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
      {A∙ : A → A → 𝒰 ℓᵃ̇} {B∙ : B → B → 𝒰 ℓᵇ̇}
      ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄
      {F   : A → B → 𝒰 ℓf}  {F⁻    : B → A → 𝒰 ℓf⁻}
      {G   : B → C → 𝒰 ℓg}  {G⁻    : C → B → 𝒰 ℓg⁻}
      {F∙G : A → C → 𝒰 ℓfg} {G⁻∙F⁻ : C → A → 𝒰 ℓg⁻f⁻}
      ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp G G⁻ B∙ ⦄
      ⦃ _ : Comp F G  F∙G ⦄ ⦃ _ : Comp G⁻ F⁻ G⁻∙F⁻ ⦄ ⦃ _ : Comp F∙G G⁻∙F⁻ A∙ ⦄
      ⦃ _ : Comp B∙ F⁻  F⁻ ⦄ ⦃ _ : Comp G G⁻∙F⁻  F⁻ ⦄
      ⦃ _ : GAssoc G G⁻  F⁻  B∙  G⁻∙F⁻  F⁻ ⦄ ⦃ _ : GAssoc F G G⁻∙F⁻ F∙G F⁻ A∙  ⦄
      ⦃ _ : GUnit-o B∙ F⁻  ⦄
    → Comp (Retract F⁻) (Retract G⁻) (Retract G⁻∙F⁻)
  Comp-Retract ._∙_ (r₁ , hs₁) (r₂ , hs₂) .fst = r₂ ∙ r₁
  Comp-Retract ._∙_ (r₁ , hs₁) (r₂ , hs₂) .snd .section = hs₁ .section ∙ hs₂ .section
  Comp-Retract ._∙_ (r₁ , hs₁) (r₂ , hs₂) .snd .is-section =
    retract-comp-helper (hs₁ .section) (hs₂ .section) r₂ r₁ (hs₂ .is-section) (hs₁ .is-section)

  Refl-Erased-Iso : Refl (Isoᴱ {ℓ})
  Refl-Erased-Iso .refl = id , qinv→qinvᴱ id-qinvₜ

  Dual-Erased-Iso : Dual (Isoᴱ {ℓ} {ℓ′}) Isoᴱ
  Dual-Erased-Iso ._ᵒᵖ (f , g , s , r) = g , f , r , s

  Comp-≅
    : ∀ {ℓᵃ ℓᵇ ℓᶜ ℓᵃ̇ ℓᵇ̇ ℓᶜ̇ ℓf ℓf⁻ ℓg ℓg⁻ ℓfg ℓg⁻f⁻}
      {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
      {F : A → B → 𝒰 ℓf}  {F⁻ : B → A → 𝒰 ℓf⁻}
      {G : B → C → 𝒰 ℓg} {G⁻ : C → B → 𝒰 ℓg⁻}
      {F∙G : A → C → 𝒰 ℓfg} {G⁻∙F⁻ : C → A → 𝒰 ℓg⁻f⁻}
      {A∙ : A → A → 𝒰 ℓᵃ̇} {B∙ : B → B → 𝒰 ℓᵇ̇} {C∙ : C → C → 𝒰 ℓᶜ̇}
      ⦃ _ : Comp F F⁻ A∙ ⦄ ⦃ _ : Comp F⁻ F  B∙ ⦄
      ⦃ _ : Comp G G⁻ B∙ ⦄ ⦃ _ : Comp G⁻ G  C∙ ⦄
      ⦃ _ : Comp F∙G G⁻∙F⁻ A∙ ⦄ ⦃ _ : Comp G⁻∙F⁻ F∙G  C∙ ⦄
      ⦃ _ : Comp F G  F∙G ⦄ ⦃ _ : Comp G⁻ F⁻ G⁻∙F⁻ ⦄
      ⦃ _ : Comp B∙ G  G ⦄ ⦃ _ : Comp F⁻ F∙G  G ⦄
      ⦃ _ : GAssoc F⁻ F  G  B∙  F∙G  G ⦄ ⦃ _ : GAssoc G⁻ F⁻ F∙G  G⁻∙F⁻ G  C∙  ⦄
      ⦃ _ : Comp G G⁻∙F⁻ F⁻ ⦄ ⦃ _ : Comp B∙ F⁻ F⁻ ⦄
      ⦃ _ : GAssoc F  G  G⁻∙F⁻ F∙G  F⁻ A∙ ⦄ ⦃ _ : GAssoc G  G⁻ F⁻ B∙  G⁻∙F⁻ F⁻ ⦄
      ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄ ⦃ _ : Refl C∙ ⦄
      ⦃ _ : GUnit-o B∙ G  ⦄ ⦃ _ : GUnit-o B∙ F⁻ ⦄
    → Comp (Iso F F⁻) (Iso G G⁻) (Iso F∙G G⁻∙F⁻)
  Comp-≅ ._∙_ i j = iso (u .fst) (v .fst) (u .snd .is-section) (v .snd .is-section)
    where
      u : Retract _ _ _
      u = (j .to , make-section (j .from) (j .inv-o)) ∙ (i .to , make-section (i .from) (i .inv-o))
      v : Retract _ _ _
      v = (i .from , make-section (i .to) (i .inv-i)) ∙ (j .from , make-section (j .to) (j .inv-i))

  Comp-Erased-Iso : Comp (Isoᴱ {ℓ} {ℓ′}) (Isoᴱ {ℓ′ = ℓ″}) Isoᴱ
  Comp-Erased-Iso ._∙_ (f , g , erase s , erase r) (f′ , g′ , erase s′ , erase r′)
    = f ∙ f′  , g′ ∙ g
    , erase (fun-ext λ x → f′ # (s  # g′ x) ∙ s′ # x)
    , erase (fun-ext λ x → g  # (r′ # f  x) ∙ r  # x)


retract-qinv→section-qinv
  : {A : Type ℓ} {B : Type ℓ′}
  → (r : Retractₜ A B) (ii : quasi-inverse (r .fst)) → quasi-inverse (r .snd .section)
retract-qinv→section-qinv (g , hs) ii .inv = g
retract-qinv→section-qinv (g , hs) ii .inverses .Inverses.inv-o =
  g ∙ hs .section ◁ ii .inv-i ⁻¹ ∙∙ g ◁ hs .is-section ▷ ii .inv ∙∙ ii .inv-i
retract-qinv→section-qinv r ii .inverses .Inverses.inv-i = r .snd .is-section

is-equiv→qinv : {f : A → B} → is-equiv f → quasi-inverse f
is-equiv→qinv eqv .inv = is-equiv→inverse eqv
is-equiv→qinv eqv .inverses .Inverses.inv-o =
  fun-ext λ y → eqv .equiv-proof y .fst .snd
is-equiv→qinv {f} eqv .inverses .Inverses.inv-i =
  fun-ext λ x → ap fst $ eqv .equiv-proof (f x) .snd (x , refl)

module _ {f : A → B} (r : quasi-inverse f) where
  open quasi-inverse r renaming ( inv   to g
                                ; inv-i to v
                                ; inv-o to u
                                )
  module _ (y : B) (x₀ x₁ : A) (p₀ : f x₀ ＝ y) (p₁ : f x₁ ＝ y) where

    private
      π₀ : g y ＝ x₀
      π₀ i = hcomp (∂ i) λ where
        k (i = i0) → g y
        k (i = i1) → v k x₀
        k (k = i0) → g (p₀ (~ i))

      θ₀ : Square (ap g (sym p₀)) refl π₀ _
      θ₀ i j = hfill (∂ i) j λ where
        k (i = i0) → g y
        k (i = i1) → v k x₀
        k (k = i0) → g (p₀ (~ i))

      π₁ : g y ＝ x₁
      π₁ i = hcomp (∂ i) λ where
        j (i = i0) → g y
        j (i = i1) → v j x₁
        j (j = i0) → g (p₁ (~ i))

      θ₁ : Square (ap g (sym p₁)) refl π₁ _
      θ₁ i j = hfill (∂ i) j λ where
        j (i = i0) → g y
        j (i = i1) → v j x₁
        j (j = i0) → g (p₁ (~ i))

      π : x₀ ＝ x₁
      π i = hcomp (∂ i) λ where
        j (j = i0) → g y
        j (i = i0) → π₀ j
        j (i = i1) → π₁ j

      θ : Square refl π₀ π π₁
      θ i j = hfill (∂ i) j λ where
        k (i = i1) → π₁ k
        k (i = i0) → π₀ k
        k (k = i0) → g y

      ι : Square (ap (g ∘ f) π) (ap g p₀) refl (ap g p₁)
      ι i j = hcomp (∂ i ∨ ∂ j) λ where
        k (k = i0) → θ i (~ j)
        k (i = i0) → θ₀ (~ j) (~ k)
        k (i = i1) → θ₁ (~ j) (~ k)
        k (j = i0) → v (~ k) (π i)
        k (j = i1) → g y

      sq₁ : Square (ap f π) p₀ refl p₁
      sq₁ i j = hcomp (∂ i ∨ ∂ j) λ where
         k (i = i0) → u k (p₀ j)
         k (i = i1) → u k (p₁ j)
         k (j = i0) → u k (f (π i))
         k (j = i1) → u k y
         k (k = i0) → f (ι i j)

    qinv→fibre-is-prop : (x₀ , p₀) ＝ (x₁ , p₁)
    qinv→fibre-is-prop i .fst = π i
    qinv→fibre-is-prop i .snd = sq₁ i

  qinv→is-equiv : is-equiv f
  qinv→is-equiv .equiv-proof y .fst .fst = g y
  qinv→is-equiv .equiv-proof y .fst .snd = u # y
  qinv→is-equiv .equiv-proof y .snd z =
    qinv→fibre-is-prop y (g y) (z .fst) (u # y) (z .snd)
  {-# INLINE qinv→is-equiv #-}


≅→≃ : A ≅ B → A ≃ B
≅→≃ i = i .to , qinv→is-equiv (make-qinv (i .from) (i .inverses))

≃→≅ : A ≃ B → A ≅ B
≃→≅ e = qinv→≅ (e .fst) (is-equiv→qinv (e .snd))
