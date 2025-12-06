{-# OPTIONS --safe --no-exact-split #-}
module Data.Maybe.Membership where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Effect

open import Logic.Discreteness

open import Functions.Embedding

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Maybe.Path
open import Data.Maybe.Operations
open import Data.Maybe.Instances.Map
open import Data.Maybe.Instances.Idiom
open import Data.Maybe.Instances.Bind
open import Data.Maybe.Correspondences.Unary.Any
open import Data.Maybe.Correspondences.Unary.All

open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

private variable
  ℓᵃ ℓ ℓ′ : Level
  A : Type ℓᵃ
  a x y : A
  xm : Maybe A

_∈ₘ_ : ∀ {ℓᵃ} {A : Type ℓᵃ}
     → A → Maybe A → Type ℓᵃ
x ∈ₘ xm = Any (x ＝_) xm

instance
  Membership-Maybe : {A : Type ℓ} → Membership A (Maybe A) ℓ
  Membership-Maybe ._∈_ = _∈ₘ_

=just→∈ : ∀ {ℓᵃ} {A : Type ℓᵃ} {x : A} {m : Maybe A}
        → m ＝ just x → x ∈ₘ m
=just→∈ {m = just x}  e = here (just-inj e ⁻¹)
=just→∈ {m = nothing} e = false! e

∈→=just : ∀ {ℓᵃ} {A : Type ℓᵃ} {x : A} {m : Maybe A}
        → x ∈ₘ m → m ＝ just x
∈→=just {m = just x}  x∈ = ap just (unhere x∈ ⁻¹)
∈→=just {m = nothing} x∈ = false! x∈

=nothing→∉ : ∀ {ℓᵃ} {A : Type ℓᵃ} {x : A} {m : Maybe A}
           → m ＝ nothing → x ∉ m
=nothing→∉ {m = just x}  e = false! e
=nothing→∉ {m = nothing} e = false!

∈ₘ-unique : ∀ {ℓᵃ} {A : Type ℓᵃ} {x y : A} {m : Maybe A}
          → x ∈ₘ m → y ∈ₘ m → x ＝ y
∈ₘ-unique x∈ y∈ = just-inj (∈→=just x∈ ⁻¹ ∙ ∈→=just y∈)

instance
  ∈ₘ-just : Reflects (x ∈ₘ just x) true
  ∈ₘ-just = ofʸ (here refl)
  {-# OVERLAPPING ∈ₘ-just #-}

has : ⦃ d : is-discrete A ⦄ → A → Maybe A → Bool
has a = any (λ x → ⌊ a ≟ x ⌋)

Reflects-has : ⦃ d : is-discrete A ⦄ {x : A} {xm : Maybe A}
             → Reflects (x ∈ xm) (has x xm)
Reflects-has ⦃ d ⦄ {x} = Reflects-any λ y → d {x} {y} .proof

instance
  Dec-∈ₘ
    : {a : A} {xm : Maybe A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈ xm)
  Dec-∈ₘ {a} {xm} .does = has a xm
  Dec-∈ₘ          .proof = Reflects-has
  {-# OVERLAPPING Dec-∈ₘ #-}

¬here→∉ : a ≠ x → ¬ (a ∈ₘ just x) -- TODO why
¬here→∉ ne (here px) = ne px

-- map

∈-map : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xm : Maybe A}
       → (f : A → B) → x ∈ xm → f x ∈ map f xm
∈-map {xm = just x} f (here e) = here (ap f e)

map-inj-∈ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xm : Maybe A}
       → (f : A → B) → Injective f
       → f x ∈ map f xm → x ∈ xm
map-inj-∈ {xm = just x} f inj (here e) = here (inj e)

map-∈Σ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {y : B} {xm : Maybe A}
        → (f : A → B)
        → y ∈ map f xm
        → Σ[ x ꞉ A ] ((x ∈ xm) × (y ＝ f x))
map-∈Σ {xm = just x} f (here e) = x , here refl , e

-- <*>

∈-<*> : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
        {f : A → B} {fm : Maybe (A → B)} {x : A} {xm : Maybe A}
      → f ∈ fm → x ∈ xm → f x ∈ (fm <*> xm)
∈-<*> {fm = just f} {xm = just x} (here ef) (here ex) = here (ap² _$_ ef ex)

<*>-∈Σ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {y : B} {fm : Maybe (A → B)} {xm : Maybe A}
       → y ∈ (fm <*> xm)
       → Σ[ f ꞉ (A → B) ] Σ[ x ꞉ A ] (f ∈ fm) × (x ∈ xm) × (f x ＝ y)
<*>-∈Σ {fm = just f} {xm = just x} (here ey) = f , x , here refl , here refl , ey ⁻¹

∈-map² : ∀ {ℓᵇ ℓᶜ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
        {f : A → B → C} {x : A} {xm : Maybe A} {y : B} {ym : Maybe B}
      → x ∈ xm → y ∈ ym → f x y ∈ map² f xm ym
∈-map² {f} {xm = just x} {ym = just y} (here ex) (here ey) = here (ap² f ex ey)

map²-∈Σ : ∀ {ℓᵇ ℓᶜ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
        {f : A → B → C} {xm : Maybe A} {ym : Maybe B} {z : C}
       → z ∈ map² f xm ym
       → Σ[ x ꞉ A ] Σ[ y ꞉ B ] (x ∈ xm) × (y ∈ ym) × (f x y ＝ z)
map²-∈Σ {xm = just x} {ym = just y} (here ez) = x , y , here refl , here refl , ez ⁻¹

-- bind

∈ₘ-bind : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {xm : Maybe A}
       → {y : B} {fm : A → Maybe B} → x ∈ xm → y ∈ fm x
       → y ∈ (xm >>= fm)
∈ₘ-bind {xm = just z} {y} {fm} (here xe) yi = subst (λ q → y ∈ₘ fm q) xe yi

bind-∈Σ : ∀ {ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {y : B} {fm : A → Maybe B} {xm : Maybe A}
       → y ∈ (xm >>= fm)
       → Σ[ x ꞉ A ] (x ∈ xm) × (y ∈ fm x)
bind-∈Σ {xm = just x} yi = x , here refl , yi

-- Any

Any→Σ∈ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm : Maybe A}
         → Any P xm
         → Σ[ x ꞉ A ] x ∈ xm × P x
Any→Σ∈ {xm = just x} (here px) = x , here refl , px

∈→Any : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm : Maybe A} {x : A}
       → x ∈ xm → P x
       → Any P xm
∈→Any {P} {xm = just y} (here e) px = here (subst P e px)

any-map∈ : {xm : Maybe A} {P : Pred A ℓ} {Q : Pred A ℓ′}
         → (∀ {x} → x ∈ xm → P x → Q x)
         → Any P xm → Any Q xm
any-map∈ f a =
  let (x , x∈ , px) = Any→Σ∈ a in
  ∈→Any x∈ (f x∈ px)

any-⊆ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm ym : Maybe A}
       → xm ⊆ ym
       → Any P xm → Any P ym
any-⊆ xsy ax =
  let (x , x∈ , px) = Any→Σ∈ ax in
  ∈→Any (xsy x∈) px

-- All

All→∀∈ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm : Maybe A}
        → All P xm
        → (x : A) → x ∈ xm → P x
All→∀∈ {P} {xm = just y} (just px) x (here e) = subst P (e ⁻¹) px

∀∈→All : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xm : Maybe A}
        → ((x : A) → x ∈ xm → P x)
        → All P xm
∀∈→All {xm = just x}  ax = just (ax x (here refl))
∀∈→All {xm = nothing} ax = nothing

{-
all-⊆ : {A : 𝒰 ℓᵃ} {P : Pred A ℓ} {xs ys : List A}
       → xs ⊆ ys → All P ys → All P xs
all-⊆ xsy ay = ∀∈→All λ x → All→∀∈ ay x ∘ xsy

all-∈-map : ∀ {ℓ′} {P : Pred A ℓ} {Q : Pred A ℓ′}
            → (∀ {x} → x ∈ xs → P x → Q x)
            → All P xs → All Q xs
all-∈-map {xs = []}     f []       = []
all-∈-map {xs = x ∷ xs} f (p ∷ ps) = f (here refl) p ∷ all-∈-map (f ∘ there) ps
-}
