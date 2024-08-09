{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Properties where

open import Meta.Prelude
open import Meta.Effect.Map
open import Meta.Extensionality

open import Functions.Constant
open import Functions.Embedding
open import Functions.Surjection

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Path
open import Data.Truncation.Propositional.Instances.Map

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  C : Type ℓ″

universal : is-prop B → (∥ A ∥₁ → B) ≃ (A → B)
universal {B} {A} B-prop = ≅→≃ $ inc′ , iso rec′ (λ _ → refl) beta where
  instance _ = hlevel-prop-instance B-prop
  inc′ : (x : ∥ A ∥₁ → B) → A → B
  inc′ f x = f ∣ x ∣₁

  rec′ : (f : A → B) → ∥ A ∥₁ → B
  rec′ f ∣ x ∣₁ = f x
  rec′ f (squash₁ x y i) = B-prop (rec′ f x) (rec′ f y) i

  beta : rec′ is-left-inverse-of inc′
  beta f = fun-ext $ elim! λ _ → refl

is-prop≃equiv-∥-∥₁ : is-prop A ≃ (A ≃ ∥ A ∥₁)
is-prop≃equiv-∥-∥₁ = prop-extₑ!
  (λ pr → to ⦃ hlevel-instance pr ⦄)
  (λ e → ≃→is-of-hlevel! 1 e)
  where
   to : ⦃ H-Level 1 A ⦄ → (A ≃ ∥ A ∥₁)
   to = prop-extₑ! ∣_∣₁ proj!


corestriction : (f : A → B) → (A → Im f)
corestriction f x = f x , ∣ x , refl ∣₁

corestriction-is-surjective : is-surjective (corestriction f)
corestriction-is-surjective (_ , p) = map (second Σ-prop-path!) p

dom-is-set→image-is-set
  : is-set B → {f : A → B} → is-set (Im f)
dom-is-set→image-is-set B-set = hlevel 2 -- hlevel!
  where instance _ = hlevel-basic-instance 2 B-set

is-constant→image-is-prop
  : is-set B → {f : A → B} → 2-Constant f → is-prop (Im f)
is-constant→image-is-prop B-set {f} f-const (a , x) (b , y) = Σ-prop-path! $ case (x , y) of
  λ f*a p f*b q → p ⁻¹ ∙∙ f-const f*a f*b ∙∙ q
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
         → ⦃ B-set : H-Level 2 B ⦄
         → ∥ A ∥₁ → B
rec-set! f-const = rec-set f-const (hlevel 2)

Σ-over-prop-∥-∥₁≃∃
  : {A : Type ℓ} {B : A → Type ℓ′} → is-prop A
  → Σ[ a ꞉ A ] ∥ B a ∥₁ ≃ ∃[ a ꞉ A ] B a
Σ-over-prop-∥-∥₁≃∃ A-prop = prop-extₑ!
  (λ x → map (x .fst ,_) (x .snd))
  (rec! λ a b → a , ∣ b ∣₁)
  where instance _ = hlevel-prop-instance A-prop

∥-∥₁-is-of-size : {X : 𝒰 ℓ}
                → is-of-size ℓ′ X → is-of-size ℓ′ ∥ X ∥₁
∥-∥₁-is-of-size = bimap ∥_∥₁ ae

instance
  Size-∥-∥₁ : {A : Type ℓ} → ⦃ _ : Size ℓ′ A ⦄ → Size ℓ′ ∥ A ∥₁
  Size-∥-∥₁ {ℓ′} .Size.has-of-size = ∥-∥₁-is-of-size (size ℓ′)

  Extensional-Σ-∥-∥₁
    : {A : Type ℓ} {B : A → Type ℓ′}
      ⦃ ea : Extensional A ℓ″ ⦄
    → Extensional (Σ[ x ꞉ A ] ∥ B x ∥₁) ℓ″
  Extensional-Σ-∥-∥₁ ⦃ ea ⦄ = Σ-prop→extensional! ea
  {-# OVERLAPPING Extensional-Σ-∥-∥₁ #-}

  Extensional-∥-∥₁-map
    : ∀ {ℓ ℓ′ ℓr} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ B-set : H-Level 2 B ⦄
    → ⦃ ea : Extensional (A → B) ℓr ⦄
    → Extensional (∥ A ∥₁ → B) ℓr
  Extensional-∥-∥₁-map ⦃ ea ⦄ =
    set-injective→extensional! (λ p → fun-ext (elim! (happly p))) ea


-- Truncated/connected factorization

_factors-through_
  : (f : A → C) (B : Type (level-of-type A ⊔ level-of-type C)) → _
_factors-through_ {A} {C} f B = Σ[ ρ ꞉ (A ↠ B) ] Σ[ ι ꞉ (B ↪ C) ] (f ＝ ι #_ ∘ ρ #_)

Factorization : (f : A → C) → _
Factorization f = Σ[ M ꞉ Type _ ] f factors-through M

image-factorization : f factors-through Im f
image-factorization {f} =
  (corestriction f , corestriction-is-surjective) , (fst , subset-proj-is-embedding (λ _ → hlevel 1)) , refl


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
  embed-is-embedding = preimage-is-prop→is-embedding go where
    go : (t : Image) (u v : Σ[ z ꞉ Image ] (embed z ＝ embed t)) → u ＝ v
    go t (x , p) (y , q) = quot (ls.from (p ∙ q ⁻¹)) ,ₚ commutes→square coh where opaque
      coh : ls.to (ls.from (p ∙ q ⁻¹)) ∙ q ＝ p ∙ refl
      coh = ap (_∙ q) (ls.ε (p ∙ q ⁻¹)) ∙ ∙-cancel-r p q ∙ ∙-id-r p ⁻¹

  elim-prop
    : ∀ {ℓ′} {P : Image → Type ℓ′}
    → (∀ x → is-prop (P x))
    → (∀ x → P ⦋ x ⦌)
    → ∀ x → P x
  elim-prop P-prop p⦋⦌ ⦋ x ⦌ = p⦋⦌ x
  elim-prop P-prop p⦋⦌ (quot {r = x} {r′ = y} p i) =
    is-prop→pathᴾ (λ i → P-prop (quot p i))
      (elim-prop P-prop p⦋⦌ x)
      (elim-prop P-prop p⦋⦌ y) i

  ⦋-⦌-is-surjective : is-surjective ⦋_⦌
  ⦋-⦌-is-surjective = elim-prop (λ _ → hlevel 1) λ x → ∣ x , refl ∣₁

  Image→Im : Image → Im f
  Image→Im x .fst = embed x
  Image→Im x .snd = elim-prop {P = λ y → ∥ fibre f (embed y) ∥₁}
    (λ _ → hlevel 1) (λ y → ∣ y , refl ∣₁) x

  Image≃Im : Image ≃ Im f
  Image≃Im .fst = Image→Im
  Image≃Im .snd .equiv-proof (x , p) = case p return (λ p → is-contr (fibre _ (x , p))) of λ where
    w → J! (λ z q → is-contr (fibre _ (z , ∣ w , q ∣₁))) (go w) where
      go : (f⁻¹x : A) → is-contr _
      go f⁻¹x = (⦋ f⁻¹x ⦌ , refl) , λ where
        (u , α) → quot (ls.encode (ap fst α ⁻¹)) ,ₚ Σ-prop-square!
          (commutes→square (ap² _∙ₚ_ (ls.ε (sym (ap fst α))) refl ∙ ∙-inv-l _ ∙ ∙-id-l _ ⁻¹))

instance
  Size-Image
    : ∀{ℓᵃ ℓᵗ ℓⁱ} {A : Type ℓᵃ} {T : Type ℓᵗ}
      ⦃ et : Extensional T ℓⁱ ⦄
      {f : A → T}
    → Size (ℓᵃ ⊔ ℓⁱ) (Im f)
  Size-Image {ℓⁱ} {A} ⦃ et ⦄ {f} .Size.has-of-size =
    Replacement.Image (et .idsᵉ) f , Replacement.Image≃Im _ _
  {-# OVERLAPPING Size-Image #-}
