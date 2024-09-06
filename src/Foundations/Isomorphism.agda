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

Isoₜ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
Isoₜ = Iso Fun Fun

instance
  ≅-Fun : ≅-notation (𝒰 ℓ) (𝒰 ℓ′) (𝒰 (ℓ ⊔ ℓ′))
  ≅-Fun ._≅_ = Isoₜ

is-invertibleᴱ : (f : A → B) → Type _
is-invertibleᴱ {A} {B} f = Σ[ inv ꞉ (B → A) ]
  ( Erased (inv section-of f)
  × Erased (inv retract-of f) )

Isoᴱ : Type ℓ → Type ℓ′ → Type _
Isoᴱ A B = Σ[ f ꞉ (A → B) ] is-invertibleᴱ f

is-equivᴱ→is-invᴱ : is-equivᴱ f → is-invertibleᴱ f
is-equivᴱ→is-invᴱ {f} eqv = is-equivᴱ→inverse eqv
                          , erase (fun-ext λ y → eqv y .fst .snd .erased)
                          , erase (fun-ext λ x → ap fst $ eqv (f x) .snd .erased (x , erase refl))

open is-invertible

is-inv→is-invᴱ : {f : A → B} → is-invertible f → is-invertibleᴱ f
is-inv→is-invᴱ fi = fi .inv , erase (fi .inv-o) , erase (fi .inv-i)

id-is-inv : is-invertible (id {A = A})
id-is-inv .inv = id
id-is-inv .inverses .Inverses.inv-o = refl
id-is-inv .inverses .Inverses.inv-i = refl

is-inv-comp : {f : A → B} {g : B → C} → is-invertible f → is-invertible g → is-invertible (f ∙ g)
is-inv-comp fi gi .inv = gi .inv ∙ fi .inv
is-inv-comp {f} {g} fi gi .inverses .Inverses.inv-o =
  (gi .inv ◁ fi .inv-o ▷ g) ∙ gi .inv-o
is-inv-comp {f} {g} fi gi .inverses .Inverses.inv-i =
  (f ◁ gi .inv-i ▷ fi .inv) ∙ fi .inv-i

instance
  Refl-Erased-Iso : Refl (Isoᴱ {ℓ})
  Refl-Erased-Iso .refl = id , is-inv→is-invᴱ id-is-inv

  Sym-Erased-Iso : Sym (Isoᴱ {ℓ} {ℓ′}) Isoᴱ
  Sym-Erased-Iso .sym (f , g , s , r) = g , f , r , s

private
  ≅∙-helper
    : ∀ {ℓᵃ ℓᵇ ℓᶜ ℓᵇ̇ ℓᶜ̇ ℓf ℓf⁻ ℓg ℓg⁻ ℓfg ℓg⁻f⁻}
      {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
      {B∙ : B → B → 𝒰 ℓᵇ̇} {C∙ : C → C → 𝒰 ℓᶜ̇}
      ⦃ _ : Refl B∙ ⦄      ⦃ _ : Refl C∙ ⦄
      {F   : A → B → 𝒰 ℓf}  {F⁻    : B → A → 𝒰 ℓf⁻}
      {G   : B → C → 𝒰 ℓg}  {G⁻    : C → B → 𝒰 ℓg⁻}
      {F∙G : A → C → 𝒰 ℓfg} {G⁻∙F⁻ : C → A → 𝒰 ℓg⁻f⁻}
      ⦃ _ : Trans F⁻ F  B∙ ⦄ ⦃ _ : Trans G⁻ G  C∙ ⦄
      ⦃ _ : Trans F G  F∙G ⦄ ⦃ _ : Trans G⁻ F⁻ G⁻∙F⁻ ⦄ ⦃ _ : Trans G⁻∙F⁻ F∙G  C∙ ⦄
      ⦃ _ : Trans B∙ G  G ⦄ ⦃ _ : Trans F⁻ F∙G  G ⦄
      ⦃ _ : Assoc F⁻ F  G  B∙  F∙G  G ⦄ ⦃ _ : Assoc G⁻ F⁻ F∙G  G⁻∙F⁻ G  C∙  ⦄
      ⦃ _ : Unit-o B∙ G  ⦄
      {a : A} {b : B} {c : C}
      (x : G⁻ c b) (y : F⁻ b a) (z : F a b) (w : G b c)
      (p : y ∙ z ＝ refl) (q : x ∙ w ＝ refl)
    → (x ∙ y) ∙ (z ∙ w) ＝ refl
  ≅∙-helper x y z w p q =
      (x ∙ y) ∙ (z ∙ w)  ~⟨ ∙-assoc x y (z ∙ w) ⟨
      x ∙ (y ∙ z ∙ w)    ~⟨ x ◁ ∙-assoc y z w ⟩
      x ∙ (y ∙ z) ∙ w    ~⟨ x ◁ p ▷ w ⟩
      x ∙ refl ∙ w       ~⟨ x ◁ ∙-id-o w ⟩
      x ∙ w              ~⟨ q ⟩
      _                  ∎

instance
  Trans-≅
    : ∀ {ℓᵃ ℓᵇ ℓᶜ ℓᵃ̇ ℓᵇ̇ ℓᶜ̇ ℓf ℓf⁻ ℓg ℓg⁻ ℓfg ℓg⁻f⁻}
      {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
      {F : A → B → 𝒰 ℓf}  {F⁻ : B → A → 𝒰 ℓf⁻}
      {G : B → C → 𝒰 ℓg} {G⁻ : C → B → 𝒰 ℓg⁻}
      {F∙G : A → C → 𝒰 ℓfg} {G⁻∙F⁻ : C → A → 𝒰 ℓg⁻f⁻}
      {A∙ : A → A → 𝒰 ℓᵃ̇} {B∙ : B → B → 𝒰 ℓᵇ̇} {C∙ : C → C → 𝒰 ℓᶜ̇}
      ⦃ _ : Trans F F⁻ A∙ ⦄ ⦃ _ : Trans F⁻ F  B∙ ⦄
      ⦃ _ : Trans G G⁻ B∙ ⦄ ⦃ _ : Trans G⁻ G  C∙ ⦄
      ⦃ _ : Trans F∙G G⁻∙F⁻ A∙ ⦄ ⦃ _ : Trans G⁻∙F⁻ F∙G  C∙ ⦄
      ⦃ _ : Trans F G  F∙G ⦄ ⦃ _ : Trans G⁻ F⁻ G⁻∙F⁻ ⦄
      ⦃ _ : Trans B∙ G  G ⦄ ⦃ _ : Trans F⁻ F∙G  G ⦄
      ⦃ _ : Assoc F⁻ F  G  B∙  F∙G  G ⦄ ⦃ _ : Assoc G⁻ F⁻ F∙G  G⁻∙F⁻ G  C∙  ⦄
      ⦃ _ : Trans G G⁻∙F⁻ F⁻ ⦄ ⦃ _ : Trans B∙ F⁻ F⁻ ⦄
      ⦃ _ : Assoc F  G  G⁻∙F⁻ F∙G  F⁻ A∙ ⦄ ⦃ _ : Assoc G  G⁻ F⁻ B∙  G⁻∙F⁻ F⁻ ⦄
      ⦃ _ : Refl A∙ ⦄ ⦃ _ : Refl B∙ ⦄ ⦃ _ : Refl C∙ ⦄
      ⦃ _ : Unit-o B∙ G  ⦄ ⦃ _ : Unit-o B∙ F⁻ ⦄
    → Trans (Iso F F⁻) (Iso G G⁻) (Iso F∙G G⁻∙F⁻)
  Trans-≅ ._∙_ i j = iso (i .to ∙ j .to) (j .from ∙ i .from)
    (≅∙-helper (j .from) (i .from) (i .to) (j .to) (i .inv-o) (j .inv-o))
    (≅∙-helper (i .to) (j .to) (j .from) (i .from) (j .inv-i) (i .inv-i))

  Trans-Erased-Iso : Trans (Isoᴱ {ℓ} {ℓ′}) (Isoᴱ {ℓ′ = ℓ″}) Isoᴱ
  Trans-Erased-Iso ._∙_ (f , g , erase s , erase r) (f′ , g′ , erase s′ , erase r′)
    = f ∙ f′  , g′ ∙ g
    , erase (fun-ext λ x → f′ # (s  # g′ x) ∙ s′ # x)
    , erase (fun-ext λ x → g  # (r′ # f  x) ∙ r  # x)

  Funlike-Erased-Iso : {A : Type ℓ} {B : Type ℓ′} → Funlike ur (Isoᴱ A B) A (λ _ → B)
  Funlike-Erased-Iso ._#_ = fst

id-composition→is-inv : (r : is-invertible f) (g : B → A) (p : f ∘ g ＝ id) → is-invertible g
id-composition→is-inv {f} r g p .inv = f
id-composition→is-inv {f} r g p .inverses .Inverses.inv-o =
  f ∙ g ◁ r .inv-i ⁻¹ ∙∙ f ◁ p ▷ r .inv ∙∙ r .inv-i
id-composition→is-inv {f} r g p .inverses .Inverses.inv-i = p

is-equiv→is-inv : {f : A → B} → is-equiv f → is-invertible f
is-equiv→is-inv eqv .inv = is-equiv→inverse eqv
is-equiv→is-inv eqv .inverses .Inverses.inv-o =
  fun-ext λ y → eqv .equiv-proof y .fst .snd
is-equiv→is-inv {f} eqv .inverses .Inverses.inv-i =
  fun-ext λ x → ap fst $ eqv .equiv-proof (f x) .snd (x , refl)

module _ {f : A → B} (r : is-invertible f) where
  open is-invertible r renaming ( inv   to g
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

    is-inv→fibre-is-prop : (x₀ , p₀) ＝ (x₁ , p₁)
    is-inv→fibre-is-prop i .fst = π i
    is-inv→fibre-is-prop i .snd = sq₁ i

  is-inv→is-equiv : is-equiv f
  is-inv→is-equiv .equiv-proof y .fst .fst = g y
  is-inv→is-equiv .equiv-proof y .fst .snd = u # y
  is-inv→is-equiv .equiv-proof y .snd z =
    is-inv→fibre-is-prop y (g y) (z .fst) (u # y) (z .snd)
  {-# INLINE is-inv→is-equiv #-}


≅→≃ : A ≅ B → A ≃ B
≅→≃ i = i .to , is-inv→is-equiv (make-invertible (i .from) (i .inverses))

≃→≅ : A ≃ B → A ≅ B
≃→≅ e = is-inv→≅ (e .fst) (is-equiv→is-inv (e .snd))
