{-# OPTIONS --safe #-}
module Truncation.Propositional.Properties where

open import Foundations.Base
  hiding (_$_; Σ-syntax; Π-syntax; ∀-syntax)
open import Foundations.Equiv
open import Foundations.Path
open import Foundations.Sigma
  hiding (Σ-syntax)

open import Meta.Effect.Map
open import Meta.Search.HLevel
open import Meta.Underlying

open import Structures.IdentitySystem.Interface

open import Functions.Constant
open import Functions.Embedding
open import Functions.Surjection

open import Truncation.Propositional.Base public
open import Truncation.Propositional.Instances.Map

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  C : Type ℓ″

elim² : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
      → (∀ x y → is-prop (P x y))
      → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
      → ∀ x y → P x y
elim² {A} {B} {P} P-prop work x y = go x y where
  go : ∀ x y → P x y
  go ∣ x ∣₁ ∣ y ∣₁ = work x y
  go ∣ x ∣₁ (squash₁ y y′ i) =
    is-prop→pathP (λ i → P-prop ∣ x ∣₁ (squash₁ y y′ i))
                  (go ∣ x ∣₁ y) (go ∣ x ∣₁ y′) i

  go (squash₁ x y i) z =
    is-prop→pathP (λ i → P-prop (squash₁ x y i) z)
                  (go x z) (go y z) i

rec² : is-prop C
     → (A → B → C)
     → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec² C-prop = elim² (λ _ _ → C-prop)

rec!
  : {@(tactic hlevel-tactic-worker) B-prop : is-prop B}
  → (A → B)
  → (x : ∥ A ∥₁) → B
rec! {B-prop} = elim (λ _ → B-prop)

rec²! : {@(tactic hlevel-tactic-worker) C-prop : is-prop C}
      → (A → B → C)
      → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec²! {C-prop} = rec² C-prop

elim!
  : {A : Type ℓ} {P : ∥ A ∥₁ → Type ℓ′}
    {@(tactic hlevel-tactic-worker) P-prop : ∀{a} → is-prop (P a)}
  → Π[ a ꞉ A ] P ∣ a ∣₁
  → (x : ∥ A ∥₁) → P x
elim! {P-prop} = elim (λ _ → P-prop)

proj!
  : {@(tactic hlevel-tactic-worker) A-prop : is-prop A}
  → ∥ A ∥₁ → A
proj! {A-prop} = rec A-prop id

elim²! : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
       → {@(tactic hlevel-tactic-worker) P-prop : ∀ x y → is-prop (P x y)}
       → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
       → ∀ x y → P x y
elim²! {P-prop} = elim² P-prop

universal : is-prop B → (∥ A ∥₁ → B) ≃ (A → B)
universal {B} {A} B-prop = iso→equiv $ inc′ , iso rec′ (λ _ → refl) beta where
  instance _ = hlevel-prop-instance B-prop
  inc′ : (x : ∥ A ∥₁ → B) → A → B
  inc′ f x = f ∣ x ∣₁

  rec′ : (f : A → B) → ∥ A ∥₁ → B
  rec′ f ∣ x ∣₁ = f x
  rec′ f (squash₁ x y i) = is-prop-β B-prop (rec′ f x) (rec′ f y) i

  beta : rec′ is-left-inverse-of inc′
  beta f = fun-ext $ elim! λ _ → refl

is-prop→equiv-∥-∥₁ : is-prop A → A ≃ ∥ A ∥₁
is-prop→equiv-∥-∥₁ A-prop = prop-extₑ! ∣_∣₁ proj!
  where instance _ = hlevel-prop-instance A-prop

is-prop≃equiv-∥-∥₁ : is-prop A ≃ (A ≃ ∥ A ∥₁)
is-prop≃equiv-∥-∥₁ {A} = prop-extₑ! is-prop→equiv-∥-∥₁ (λ e → is-of-hlevel-≃ 1 e hlevel!)

corestriction : (f : A → B) → (A → Im f)
corestriction f x = f x , ∣ x , refl ∣₁

corestriction-is-surjective : is-surjective (corestriction f)
corestriction-is-surjective (_ , p) = map (second Σ-prop-path!) p

dom-is-set→image-is-set
  : is-set B → {f : A → B} → is-set (Im f)
dom-is-set→image-is-set B-set = hlevel!
  where instance _ = hlevel-basic-instance 2 B-set

is-constant→image-is-prop
  : is-set B → {f : A → B} → 2-Constant f → is-prop (Im f)
is-constant→image-is-prop B-set {f} f-const = is-prop-η λ (a , x) (b , y) →
  Σ-prop-path! $ elim²! (λ { (f*a , p) (f*b , q) → sym p ∙∙ f-const f*a f*b ∙∙ q }) x y
  where instance _ = hlevel-basic-instance 2 B-set

-- TODO if codomain is an n-type, we should require f to be n-constant
-- write a generic recursor
rec-set : {f : A → B}
        → 2-Constant f
        → is-set B
        → ∥ A ∥₁ → B
rec-set f-const B-set = fst ∘ elim
  (λ _ → is-constant→image-is-prop B-set f-const) (corestriction _)

rec-set! : {f : A → B}
         → 2-Constant f
         → {@(tactic hlevel-tactic-worker) B-set : is-set B}
         → ∥ A ∥₁ → B
rec-set! f-const {B-set} = rec-set f-const B-set

Σ-∥-∥₁-over-prop
  : {A : Type ℓ} {B : A → Type ℓ′} → is-prop A
  → Σ[ a ꞉ A ] ∥ B a ∥₁ ≃ ∥ Σ[ a ꞉ A ] B a ∥₁
Σ-∥-∥₁-over-prop A-prop = prop-extₑ!
  (λ x → map (x .fst ,_) (x .snd))
  (rec! (second ∣_∣₁)) where instance _ = hlevel-prop-instance A-prop


_factors-through_
  : (f : A → C) (B : Type (level-of-type A ⊔ level-of-type C)) → _
_factors-through_ {A} {C} f B = Σ[ ρ ꞉ (A ↠ B) ] Σ[ ι ꞉ (B ↪ C) ] (f ＝ (ι $_) ∘ (ρ $_))

Factorization : (f : A → C) → _
Factorization f = Σ[ M ꞉ Type _ ] f factors-through M

image-factorization : f factors-through Im f
image-factorization {f} =
  (corestriction f , corestriction-is-surjective) , (fst , subset-proj-is-embedding hlevel!) , refl


module Replacement
  {ℓᵃ ℓᵗ ℓⁱ} {A : Type ℓᵃ} {T : Type ℓᵗ}
  {_~_ : T → T → Type ℓⁱ} {rfl : ∀ x → x ~ x}
  (locally-small : is-identity-system _~_ rfl)
  (f : A → T)
  where

  private module ls = IdS locally-small

  data Image : Type (ℓᵃ ⊔ ℓⁱ)
  embed : Image → T

  -- HIRTs are coherent by definition in this sense
  -- https://homotopytypetheory.org/2014/06/08/hiru-tdd/
  data Image where
    ⦋_⦌   : A → Image
    quot : ∀ {r r′} → embed r ~ embed r′ → r ＝ r′

  embed ⦋ x ⦌ = f x
  embed (quot p i) = ls.decode p i

  embed-is-embedding : is-embedding embed
  embed-is-embedding = (preimage-is-prop→is-embedding ∘ (is-prop-η ∘_)) go where
    go : _
    go t (x , p) (y , q) = Σ-pathP (quot (ls.from (p ∙ sym q))) (commutes→square coh) where opaque
      coh : ls.to (ls.from (p ∙ sym q)) ∙ q ＝ p ∙ refl
      coh = ap (_∙ q) (ls.ε (p ∙ sym q)) ∙ ∙-cancel-r p q ∙ sym (∙-id-r p)

  elim-prop
    : ∀ {ℓ′} {P : Image → Type ℓ′}
    → (∀ x → is-prop (P x))
    → (∀ x → P ⦋ x ⦌)
    → ∀ x → P x
  elim-prop P-prop p⦋⦌ ⦋ x ⦌ = p⦋⦌ x
  elim-prop P-prop p⦋⦌ (quot {r = x} {r′ = y} p i) =
    is-prop→pathP (λ i → P-prop (quot p i))
      (elim-prop P-prop p⦋⦌ x)
      (elim-prop P-prop p⦋⦌ y) i

  ⦋-⦌-is-surjective : is-surjective ⦋_⦌
  ⦋-⦌-is-surjective = elim-prop hlevel! λ x → ∣ x , refl ∣₁

  Image→Im : Image → Im f
  Image→Im x .fst = embed x
  Image→Im x .snd = elim-prop {P = λ y → ∥ fibre f (embed y) ∥₁}
    hlevel! (λ y → ∣ y , refl ∣₁) x

  Image≃Im : Image ≃ Im f
  Image≃Im .fst = Image→Im
  Image≃Im .snd .equiv-proof (x , p) = is-contr-β $ elim! {P = λ p → is-contr (fibre _ (x , p))}
    (λ { (w , p) → J (λ z q → is-contr (fibre _ (z , ∣ w , q ∣₁))) (go w) p }) p where
      go : (f⁻¹x : A) → is-contr _
      go f⁻¹x = is-contr-η $ (⦋ f⁻¹x ⦌ , refl) , λ where
        (u , α) → Σ-pathP (quot (ls.encode (sym (ap fst α)))) $
                          Σ-prop-square hlevel! $ commutes→square $
                            ap² _∙_ (ls.ε (sym (ap fst α))) refl ∙ ∙-inv-l _ ∙ sym (∙-id-l _)
