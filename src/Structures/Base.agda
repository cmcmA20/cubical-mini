{-# OPTIONS --safe #-}
module Structures.Base where

open import Meta.Prelude
open import Meta.Extensionality
open import Meta.Record

open import Functions.Embedding
open import Functions.Equiv.Weak

open import Data.Unit.Base
open import Data.Unit.Properties

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

-- surprise tool that will help us later
record Total-hom
  {ℓᵃ ℓᵃ̇ ℓᵇ ℓᵇ̇ o ℓ}
  {A : Type ℓᵃ} {B : Type ℓᵇ}
  (F : A → B → Type o)
  {M : A → Type ℓᵃ̇} {N : B → Type ℓᵇ̇}
  (H : {x : A} {y : B} → F x y → M x → N y → 𝒰 ℓ)
  {a : A} {b : B} (S : M a) (T : N b) : Type (o ⊔ ℓ) where
  constructor total-hom
  field
    hom       : F a b
    preserves : H hom S T

unquoteDecl Total-hom-Iso = declare-record-iso Total-hom-Iso (quote Total-hom)

open Total-hom

total-hom-path
  : ∀ {ℓᵃ ℓᵃ̇ ℓᵇ ℓᵇ̇ o ℓ}
    {A : Type ℓᵃ} {B : Type ℓᵇ}
    {F : A → B → Type o}
    {M : A → Type ℓᵃ̇} {N : B → Type ℓᵇ̇}
    {H : {x : A} {y : B} → F x y → M x → N y → 𝒰 ℓ}
    {a : A} {b : B} {S : M a} {T : N b}
    {f g : Total-hom F H S T}
  → (p : f .hom ＝ g .hom)
  → ＜ f .preserves ／ (λ i → H (p i) S T) ＼ g .preserves ＞
  → f ＝ g
total-hom-path p _  i .hom = p i
total-hom-path _ p′ i .preserves = p′ i

total-hom-pathᴾ
  : ∀ {ℓᵃ ℓᵃ̇ ℓᵇ ℓᵇ̇ o ℓ}
    {A : Type ℓᵃ} {B : Type ℓᵇ}
    {F : A → B → Type o}
    {M : A → Type ℓᵃ̇} {N : B → Type ℓᵇ̇}
    {H : {x : A} {y : B} → F x y → M x → N y → 𝒰 ℓ}
    {a a′ : A} {b b′ : B} {S : M a} {T : N b} {S′ : M a′} {T′ : N b′}
    {f : Total-hom F H S T} {g : Total-hom F H S′ T′}
  → (p : a ＝ a′) (p′ : ＜ S ／ (λ i → M (p i)) ＼ S′ ＞)
  → (q : b ＝ b′) (q′ : ＜ T ／ (λ i → N (q i)) ＼ T′ ＞)
  → (r : ＜ f .hom ／ (λ i → F (p i) (q i)) ＼ g .hom ＞)
  → ＜ f .preserves ／ (λ i → H (r i) (p′ i) (q′ i)) ＼ g .preserves ＞
  → ＜ f ／ (λ i → Total-hom F H (p′ i) (q′ i)) ＼ g ＞
total-hom-pathᴾ p p′ q q′ r r′ i .hom = r i
total-hom-pathᴾ p p′ q q′ r r′ i .preserves = r′ i

instance
  Refl-Total-hom
    : ∀{ℓᵃ ℓᵃ̇ o ℓ} {A : Type ℓᵃ} {M : A → Type ℓᵃ̇}
      {F : A → A → Type o}
      {a : A} {H : ∀{x y} → F x y → M x → M y → 𝒰 ℓ}
      ⦃ _ : Refl F ⦄ ⦃ _ : Refl (H {a} refl) ⦄
    → Refl {A = M a} (Total-hom F H)
  Refl-Total-hom .refl .hom = refl
  Refl-Total-hom .refl .preserves = refl

  Comp-Total-hom
    : ∀{ℓᵃ ℓᵇ ℓᶜ ℓᵃ̇ ℓᵇ̇ ℓᶜ̇ ℓf ℓg ℓfg ℓ ℓ′ ℓ″} {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
      {M : A → Type ℓᵃ̇} {N : B → Type ℓᵇ̇} {K : C → Type ℓᶜ̇}
      {F : A → B → Type ℓf} {G : B → C → Type ℓg}
      {F∙G : A → C → Type ℓfg}
      {a : A} {b : B} {c : C}
      {H  : ∀{x y} → F x y → M x → N y → 𝒰 ℓ}
      {H′ : ∀{x y} → G x y → N x → K y → 𝒰 ℓ′}
      {H″ : ∀{x y} → F∙G x y → M x → K y → 𝒰 ℓ″}
      ⦃ _ : Comp F G F∙G ⦄ ⦃ _ : ∀ {x y f g} → Comp (H {x} f) (H′ {y} g) (H″ (f ∙ g)) ⦄
    → Comp {A = M a} {B = N b} {C = K c} (Total-hom F H) (Total-hom G H′) (Total-hom F∙G H″)
  Comp-Total-hom ._∙_ p q .hom = p .hom ∙ q .hom
  Comp-Total-hom ._∙_ p q .preserves = p .preserves ∙ q .preserves

  Funlike-Total-hom
    : ∀{ℓᵃ ℓᵇ ℓᵃ̇ ℓᵇ̇ o ℓ ℓˣ ℓʸ} {A : Type ℓᵃ} {B : Type ℓᵇ}
      {M : A → Type ℓᵃ̇} {N : B → Type ℓᵇ̇}
      {F : A → B → Type o}
      {a : A} {b : B} {H : ∀{x y} → F x y → M x → N y → 𝒰 ℓ}
      {m : M a} {n : N b}
      {X : Type ℓˣ} {Y : F a b × X → Type ℓʸ}
    → ⦃ i : Funlike ur (F a b) X Y ⦄
    → Funlike ur (Total-hom F H m n) X (Y ∘ first hom)
  Funlike-Total-hom ._#_ f x = f .Total-hom.hom # x

  Extensional-Total-hom
    : ∀{ℓᵃ ℓᵇ ℓᵃ̇ ℓᵇ̇ o ℓ ℓʳ} {A : Type ℓᵃ} {B : Type ℓᵇ}
      {M : A → Type ℓᵃ̇} {N : B → Type ℓᵇ̇}
      {F : A → B → Type o}
      {a : A} {b : B} {H : ∀{x y} → F x y → M x → N y → 𝒰 ℓ}
      {m : M a} {n : N b}
      ⦃ sa : Extensional (F a b) ℓʳ ⦄
      ⦃ h : ∀ {x} → H-Level 1 (H x m n) ⦄
    → Extensional (Total-hom F H m n) ℓʳ
  Extensional-Total-hom ⦃ sa ⦄ = ≅→extensional Total-hom-Iso (Σ-prop→extensional! sa)



record Structure {ℓ₁ ℓ₂} (ℓ₃ : _)
  (S : Type ℓ₁ → Type ℓ₂) : Type (ℓsuc (ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂) where

  constructor HomT→Str
  field is-hom : (A B : Σₜ _ S) → (A .fst ≃ B .fst) → Type ℓ₃

open Structure public

Type-with : Structure ℓ S → Type _
Type-with {S} _ = Σₜ _ S

@0 is-univalent : Structure ℓ S → Type _
is-univalent {S} ι =
  ∀ {X Y}
  → (f : X .fst ≃ Y .fst)
  → ι .is-hom X Y f ≃ ＜ X .snd ／ (λ i → S (ua f i)) ＼ Y .snd ＞

-- σ-homomorphic equivalences
_≃s[_]_ : Σₜ _ S → Structure ℓ S → Σₜ _ S → Type _
A ≃s[ σ ] B = Σ[ f ꞉ A .fst ≃ B .fst ] (σ .is-hom A B f)

private variable σ : Structure ℓ S

-- The Structure Identity Principle says that, if `S` is a `univalent
-- structure`, then the path space of `Σ S` is equivalent to the space of
-- S-homomorphic equivalences of types. Using groups as a grounding
-- example: identification of groups is group isomorphism.
@0 SIP : is-univalent σ → {X Y : Σₜ _ S}
       → (X ≃s[ σ ] Y) ≃ (X ＝ Y)
SIP {S} {σ} is-univ {X} {Y} =
  X ≃s[ σ ] Y                                                          ~⟨⟩
  Σ[ e ꞉ X .fst ≃  Y .fst ] (σ .is-hom X Y e)                          ~⟨ Σ-ap (ua , univalence⁻¹) is-univ ⟩
  Σ[ p ꞉ X .fst ＝ Y .fst ] ＜ X .snd ／ (λ i → S (p i)) ＼ Y .snd ＞  ~⟨ ≅→≃ Σ-pathᴾ-iso ⟩
  X ＝ Y                                                               ∎

@0 sip : is-univalent σ → {X Y : Σₜ _ S} → (X ≃s[ σ ] Y) → (X ＝ Y)
sip is-univ = SIP is-univ .fst

Equiv-action : (S : Type ℓ → Type ℓ₁) → Type _
Equiv-action {ℓ} S = {X Y : Type ℓ} → (X ≃ Y) → (S X ≃ S Y)

action→structure : Equiv-action S → Structure _ S
action→structure act .is-hom (A , x) (B , y) f = act f .fst x ＝ y

@0 is-transport-str : {S : Type ℓ → Type ℓ₁} → Equiv-action S → Type _
is-transport-str {ℓ} {S} act =
  {X Y : Type ℓ} (e : X ≃ Y) (s : S X) → act e .fst s ＝ subst S (ua e) s

preserves-id : {S : Type ℓ → Type ℓ} → Equiv-action S → Type _
preserves-id {ℓ} {S} act =
  {X : Type ℓ} (s : S X) → act refl .fst s ＝ s

@0 preserves-id→is-transport-str
  : (σ : Equiv-action S)
  → preserves-id σ → is-transport-str σ
preserves-id→is-transport-str {S} σ pres-id e s =
  Jₑ (λ _ e → σ e .fst s ＝ subst S (ua e) s) lemma′ e where
    lemma′ : σ refl .fst s ＝ subst S (ua refl) s
    lemma′ =
      σ refl .fst s        ~⟨ pres-id s ⟩
      s                    ~⟨ transport-refl _ ⟨
      transport refl s     ~⟨ ap (λ p → subst S p s) ua-idₑ ⟨
      subst S (ua refl) s  ∎

@0 sym-transport-str
  : (α : Equiv-action S) (τ : is-transport-str α)
    {X Y : Type ℓ} (e : X ≃ Y) (t : S Y)
  → is-equiv→inverse (α e .snd) t ＝ subst S (sym (ua e)) t
sym-transport-str {S} α τ e t =
     sym (transport⁻-transport (ap S (ua e)) (from t))
  ∙∙ sym (ap (subst S (sym (ua e))) (τ e (from t)))
  ∙∙ ap (subst S (sym (ua e))) (ε # t)
  where open module ae = Equiv (α e)

@0 is-transport→is-univalent : (a : Equiv-action S)
                             → is-transport-str a
                             → is-univalent (action→structure a)
is-transport→is-univalent {S} act is-tr {X , s} {Y , t} eqv =
  act eqv .fst s ＝ t                   ~⟨ =→≃ (ap (_＝ t) (is-tr eqv s)) ⟩
  subst S (ua eqv) s ＝ t               ~⟨ =→≃ (pathᴾ=path (λ i → S (ua eqv i)) s t) ⟨
  ＜ s ／ (λ i → S (ua eqv i)) ＼ t ＞  ∎


constant-str : (A : Type ℓ) → Structure {ℓ₁} ℓ (λ _ → A)
constant-str T .is-hom (A , x) (B , y) f = x ＝ y

constant-str-is-univalent : is-univalent (constant-str {ℓ₁ = ℓ₁} A)
constant-str-is-univalent _ = refl

constant-action : (A : Type ℓ) → Equiv-action {ℓ = ℓ₁} (λ X → A)
constant-action _ _ = refl

constant-action-is-transport
  : is-transport-str {ℓ = ℓ₁} (constant-action A)
constant-action-is-transport _ _ = transport-refl _ ⁻¹


pointed-str : Structure ℓ id
pointed-str .is-hom (_ , x) (_ , y) f = f # x ＝ y

@0 pointed-str-is-univalent : is-univalent (pointed-str {ℓ})
pointed-str-is-univalent f = ua-pathᴾ≃= _

opaque
  unfolding ua
  id-action-is-transport : is-transport-str {ℓ} {ℓ} id
  id-action-is-transport _ _ = transport-refl _ ⁻¹

Type∙ : ∀ ℓ → Type (ℓsuc ℓ)
Type∙ _ = Type-with pointed-str


product-str : Structure ℓ S → Structure ℓ₂ T → Structure _ (λ X → S X × T X)
product-str S T .is-hom (A , x , y) (B , x′ , y′) f =
  S .is-hom (A , x) (B , x′) f × T .is-hom (A , y) (B , y′) f

@0 product-str-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                            → is-univalent σ → is-univalent τ
                            → is-univalent (product-str σ τ)
product-str-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ {X , x , y} {Y , x′ , y′} f =
  σ .is-hom (X , x) (Y , x′) f × τ .is-hom (X , y) (Y , y′) f               ~⟨ ×-ap (θ₁ f) (θ₂ f) ⟩
  ＜ x ／ (λ i → S (ua f i)) ＼ x′ ＞ × ＜ y ／ (λ i → T (ua f i)) ＼ y′ ＞  ~⟨ ≅→≃ Σ-pathᴾ-iso ⟩
  ＜ x , y ／ (λ i → S (ua f i) × T (ua f i)) ＼ x′ , y′ ＞                  ∎

product-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X × T X)
product-action actx acty eqv = ×-ap (actx eqv) (acty eqv)

@0 product-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (product-action α β)
product-action-is-transport α-tr β-tr e s = α-tr e (s .fst) ,ₚ β-tr e (s .snd)


-- naive one, do not use
private
  function-str′ : Structure ℓ₁ S → Structure ℓ₂ T → Structure _ (λ X → S X → T X)
  function-str′ {S} σ τ .is-hom (A , f) (B , g) h =
    {s : S A} {t : S B} → σ .is-hom (A , s) (B , t) h
                        → τ .is-hom (A , f s) (B , g t) h

  @0 function-str′-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                                → is-univalent σ → is-univalent τ
                                → is-univalent (function-str′ σ τ)
  function-str′-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ eqv =
    ∀-cod-≃ (λ s → ∀-cod-≃ λ t → function-≃ (θ₁ eqv) (θ₂ eqv)) ∙ fun-ext-dep-≃


function-str : Equiv-action S → Structure ℓ T → Structure _ (λ X → S X → T X)
function-str {S} act str .is-hom (A , f) (B , g) e =
  Π[ s ꞉ S A ] str .is-hom (A , f s) (B , g (act e .fst s)) e

@0 function-str-is-univalent
  : (α : Equiv-action S) → is-transport-str α
  → (τ : Structure ℓ T) → is-univalent τ
  → is-univalent (function-str α τ)
function-str-is-univalent {S} {T} α α-tr τ τ-univ {X , f} {Y , g} eqv =
  Π[ s ꞉ S X ] τ .is-hom (X , f s) (Y , _) eqv         ~⟨ Π-cod-≃ (λ s → τ-univ eqv ∙ =→≃ (ap (Pathᴾ (λ i → T (ua eqv i)) (f s) ∘ g) (α-tr _ _))) ⟩
  Π[ s ꞉ S X ] ＜ f s ／ (λ i → T (ua eqv i)) ＼ _ ＞  ~⟨ hetero-homotopy≃homotopy ⁻¹ ∙ fun-ext-dep-≃ ⟩
  _                                                    ∎

function-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X → T X)
function-action actx acty eqv = function-≃ (actx eqv) (acty eqv)

@0 function-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (function-action α β)
function-action-is-transport {S} {α} {β} α-tr β-tr eqv f =
  fun-ext λ x → ap (β eqv .fst ∘ f) (sym-transport-str α α-tr eqv x)
              ∙ β-tr eqv (f (subst S (ua eqv ⁻¹) x))


property : (S : Type ℓ → Type ℓ₁) → (∀ A → is-prop (S A)) → Structure 0ℓ S
property _ _ .is-hom _ _ _ = ⊤

@0 property-is-univalent : {S-prop : _} → is-univalent {S = S} (property S S-prop)
property-is-univalent {S-prop} {X = _ , s} {Y = _ , t} _ = _ᵒᵖ $ is-contr→equiv-⊤ $
  inhabited-prop-is-contr (is-prop→pathᴾ (λ _ → S-prop _) s t)
                          (pathᴾ-is-of-hlevel-same 1 (S-prop _))

@0 transfer-property
  : {S-prop : _}
  → (A : Type-with (property S S-prop)) (B : Type ℓ)
  → A .fst ≃ B
  → S B
transfer-property {S} A B eqv = subst S (ua eqv) (A .snd)

-- TODO use `property`?
module _
  (σ : Structure ℓ S)
  (axioms : (X : _) → S X → Type ℓ₃)
  where

  axiom-str : Structure ℓ (λ X → Σ[ s ꞉ S X ] (axioms X s))
  axiom-str .is-hom (A , s , a) (B , t , b) f =
    σ .is-hom (A , s) (B , t) f

  module _
    (univ : is-univalent σ)
    (axioms-prop : ∀ {X} {s} → is-prop (axioms X s)) where opaque

    @0 axiom-str-univalent : is-univalent axiom-str
    axiom-str-univalent {X = A , s , a} {Y = B , t , b} f =
      σ .is-hom (A , s) (B , t) f
        ~⟨ univ f ⟩
      ＜ s ／ (λ i → S (ua f i)) ＼ t ＞
        ~⟨ Σ-contract-snd (λ x → pathᴾ-is-of-hlevel-same 0 (b , axioms-prop b)) ⟨
      Σ[ p ꞉ ＜ s ／ (λ i → S (ua f i)) ＼ t ＞ ] ＜ a ／ (λ i → axioms (ua f i) (p i)) ＼ b ＞
        ~⟨ ≅→≃ Σ-pathᴾ-iso ⟩
      _
        ∎

@0 transfer-axioms
  : {σ : Structure ℓ S} {univ : is-univalent σ}
    {axioms : (X : _) → S X → Type ℓ₃}
  → (A : Type-with (axiom-str σ axioms)) (B : Type-with σ)
  → (A .fst , A .snd .fst) ≃s[ σ ] B
  → axioms (B .fst) (B .snd)
transfer-axioms {univ} {axioms} A B eqv =
  subst (axioms $ₜ²_) (sip univ eqv) (A .snd .snd)
