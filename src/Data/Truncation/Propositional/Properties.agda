{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Properties where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Extensionality
open import Foundations.Sigma

open import Functions.Constant
open import Functions.Embedding
open import Functions.Surjection

open import Data.Empty.Base
  using (⊥ₜ ; ¬ₜ_ ; contra)

open import Data.Sum.Base
  using ([_,_]ᵤ; map-l; map-r; inl; inr)
open import Data.Sum.Properties hiding (universal)

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Path
open import Data.Truncation.Propositional.Instances.Map

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  C : Type ℓ″
  D : Type ℓ‴

universal : is-prop B → (∥ A ∥₁ → B) ≃ (A → B)
universal {B} {A} B-prop = ≅→≃ $ iso inc′ rec′ refl (fun-ext beta) where
  instance _ = hlevel-prop-instance B-prop
  inc′ : (x : ∥ A ∥₁ → B) → A → B
  inc′ f x = f ∣ x ∣₁

  rec′ : (f : A → B) → ∥ A ∥₁ → B
  rec′ = rec B-prop

  beta : rec′ retraction-of′ inc′
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
  Size-∥-∥₁ : {A : Type ℓ} ⦃ _ : Size ℓ′ A ⦄ → Size ℓ′ ∥ A ∥₁
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

-- ⊎₁ properties

⊎₁-ap : A ≃ B → C ≃ D → (A ⊎₁ C) ≃ (B ⊎₁ D)
⊎₁-ap ab = ae ∘ ⊎-ap ab

⊎₁-ap-l : A ≃ B → (A ⊎₁ C) ≃ (B ⊎₁ C)
⊎₁-ap-l f = ⊎₁-ap f refl

⊎₁-ap-r : B ≃ C → (A ⊎₁ B) ≃ (A ⊎₁ C)
⊎₁-ap-r f = ⊎₁-ap refl f

⊎₁-comm : (A ⊎₁ B) ≃ (B ⊎₁ A)
⊎₁-comm = ae ⊎-comm

⊎₁-assoc : ((A ⊎₁ B) ⊎₁ C) ≃ (A ⊎₁ (B ⊎₁ C))
⊎₁-assoc =
  prop-extₑ!
    (rec! [ map (map-r (∣_∣₁ ∘ inl))
          , (λ c → ∣ inr ∣ inr c ∣₁ ∣₁)
          ]ᵤ)
    (rec! [ (λ a → ∣ inl ∣ inl a ∣₁ ∣₁)
          , map (map-l (∣_∣₁ ∘ inr))
          ]ᵤ)

⊎₁-idem : A ⊎₁ A ≃ ∥ A ∥₁
⊎₁-idem = prop-extₑ! (map [ id , id ]ᵤ) (map inl)

-- TODO factor through flatten
⊎₁-trunc-l : A ⊎₁ B ≃ ∥ A ∥₁ ⊎₁ B
⊎₁-trunc-l =
  prop-extₑ!
    (rec! [ (λ a → ∣ inl ∣ a ∣₁ ∣₁) , (λ b → ∣ inr b ∣₁) ]ᵤ )
    (rec! [ map inl , (λ b → ∣ inr b ∣₁) ]ᵤ)

⊎₁-trunc-r : A ⊎₁ B ≃ A ⊎₁ ∥ B ∥₁
⊎₁-trunc-r =
  prop-extₑ!
    (rec! [ (λ a → ∣ inl a ∣₁) , (λ b → ∣ inr ∣ b ∣₁ ∣₁) ]ᵤ )
    (rec! [ (λ a → ∣ inl a ∣₁) , map inr ]ᵤ)

⊎₁-¬-distribute : (¬ (A ⊎₁ B)) ≃ (¬ A) × (¬ B)
⊎₁-¬-distribute = universal (hlevel 1) ∙ ⊎-¬-distribute

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
      coh = (ls.ε # (p ∙ q ⁻¹) ▷ q) ∙ ∙-cancel-r p q ∙ ∙-id-i p ⁻¹

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
          (commutes→square (ap² _∙ₚ_ (ls.ε # sym (ap fst α)) refl ∙ ∙-inv-o _ ∙ ∙-id-o _ ⁻¹))

  Size-Im : Size (ℓᵃ ⊔ ℓⁱ) (Im f)
  Size-Im .Size.has-of-size = Image , Image≃Im
