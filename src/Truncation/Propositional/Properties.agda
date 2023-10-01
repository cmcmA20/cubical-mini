{-# OPTIONS --safe #-}
module Truncation.Propositional.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Path
open import Foundations.Sigma


open import Meta.Search.HLevel

open import Structures.IdentitySystem.Interface

open import Functions.Constant
open import Functions.Embedding
open import Functions.Surjection

open import Truncation.Propositional.Base public

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
  : {P : ∥ A ∥₁ → Type ℓ′}
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
  instance _ = B-prop
  inc′ : (x : ∥ A ∥₁ → B) → A → B
  inc′ f x = f ∣ x ∣₁

  rec′ : (f : A → B) → ∥ A ∥₁ → B
  rec′ f ∣ x ∣₁ = f x
  rec′ f (squash₁ x y i) = is-prop-β B-prop (rec′ f x) (rec′ f y) i

  beta : rec′ is-left-inverse-of inc′
  beta f = fun-ext $ elim! λ _ → refl

is-prop→equiv-∥-∥₁ : is-prop A → A ≃ ∥ A ∥₁
is-prop→equiv-∥-∥₁ A-prop = prop-extₑ! ∣_∣₁ proj!
  where instance _ = A-prop

is-prop≃equiv-∥-∥₁ : is-prop A ≃ (A ≃ ∥ A ∥₁)
is-prop≃equiv-∥-∥₁ {A} = prop-extₑ! is-prop→equiv-∥-∥₁ (λ e → is-of-hlevel-≃ 1 e hlevel!)

corestriction : (f : A → B) → (A → Im f)
corestriction f x = f x , ∣ x , refl ∣₁

corestriction-is-surjective : is-surjective (corestriction f)
corestriction-is-surjective (_ , p) = map (second Σ-prop-path!) p

dom-is-set→image-is-set
  : is-set B → {f : A → B} → is-set (Im f)
dom-is-set→image-is-set B-set = Σ-is-of-hlevel 2 B-set λ _ → ∥-∥₁-is-of-hlevel 1

is-constant→image-is-prop
  : is-set B → {f : A → B} → 2-Constant f → is-prop (Im f)
is-constant→image-is-prop B-set {f} f-const = is-prop-η λ (a , x) (b , y) →
  Σ-prop-path! $ elim²! (λ { (f*a , p) (f*b , q) → sym p ∙∙ f-const f*a f*b ∙∙ q }) x y
  where instance _ = B-set

-- TODO if codomain is an n-type, we should require f to be n-constant
-- write a generic recursor
rec-set : {f : A → B}
        → 2-Constant f
        → is-set B
        → ∥ A ∥₁ → B
rec-set f-const B-set = fst ∘ elim
  (λ _ → is-constant→image-is-prop B-set f-const) (corestriction _)

Σ-∥-∥₁-over-prop
  : {B : A → Type ℓ′} → is-prop A
  → Σ[ a ꞉ A ] ∥ B a ∥₁ ≃ ∥ Σ[ a ꞉ A ] B a ∥₁
Σ-∥-∥₁-over-prop A-prop = prop-extₑ!
  (λ x → map (x .fst ,_) (x .snd))
  (rec! (second ∣_∣₁)) where instance _ = A-prop


_factors-through_
  : (f : A → C) (B : Type (level-of-type A ⊔ level-of-type C)) → _
_factors-through_ {A} {C} f B = Σ[ ρ ꞉ (A ↠ B) ] Σ[ ι ꞉ (B ↪ C) ] (f ＝ ι .fst ∘ ρ .fst)

Factorization : (f : A → C) → _
Factorization f = Σ[ M ꞉ Type _ ] f factors-through M

image-factorization : f factors-through Im f
image-factorization {f} =
  (corestriction f , corestriction-is-surjective) , (fst , subset-proj-is-embedding hlevel!) , refl


-- TODO understand the details thoroughly + refactor, 1lab
module Replacement
  {ℓᵃ ℓᵗ ℓⁱ} {A : Type ℓᵃ} {T : Type ℓᵗ}
  {_~_ : T → T → Type ℓⁱ} {rfl : ∀ x → x ~ x}
  (locally-small : is-identity-system _~_ rfl)
  (f : A → T)
  where

  private module ls = IdS locally-small

  data Image : Type (ℓᵃ ⊔ ℓⁱ)
  embed : Image → T

  data Image where
    ⦋_⦌   : A → Image
    quot : ∀ {r r′} → embed r ~ embed r′ → r ＝ r′
    coh  : ∀ r → quot (rfl (embed r)) ＝ refl

  embed ⦋ x ⦌ = f x
  embed (quot p i) = ls.to p i
  embed (coh r i j) = ls.to-refl {a = embed r} i j

  embed-is-embedding : is-embedding embed
  embed-is-embedding = cancellable→is-embedding λ {x y} →
    iso→equiv $ from , iso (ap embed) ri ls.ε where

    from : ∀ {x y} → embed x ＝ embed y → x ＝ y
    from p = quot (ls.from p)

    ri : ∀ {x y} → (ap {x = x} {y = y} embed) is-right-inverse-of from
    ri = J (λ _ p → from (ap embed p) ＝ p) (ap quot (transport-refl _) ∙ coh _)

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
  elim-prop P-prop p⦋⦌ (coh r i j) =
    is-prop→squareP (λ i j → P-prop (coh r i j))
      (is-prop→pathP (λ i → P-prop _) _ _)
      (λ _ → elim-prop P-prop p⦋⦌ r)
      (λ _ → elim-prop P-prop p⦋⦌ r)
      (λ _ → elim-prop P-prop p⦋⦌ r) i j

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
        (u , α) → Σ-pathP (quot (ls.from (sym (ap fst α)))) $
                          Σ-prop-square hlevel! $ commutes→square $
                            ap² _∙_ (ls.ε (sym (ap fst α))) refl ∙ ∙-inv-l _ ∙ sym (∙-id-l _)


-- ????

open import Foundations.Univalence
@0 Code″ : {f : A → B} → (U V : Factorization f) → Type _
Code″ {A} {B} {f} (X , (ρ₁ , _) , (ι₁ , _) , H₁) (Y , (ρ₂ , _) , (ι₂ , _) , H₂) =
  Σ[ e ꞉ X ≃ Y ]
  Σ[ ζ ꞉ ＜ ρ₁ ／ (λ i → A → ua e i) ＼ ρ₂ ＞ ]
  Σ[ ξ ꞉ ＜ ι₁ ／ (λ i → ua e i → B) ＼ ι₂ ＞ ]
  ＜ H₁ ／ (λ i → f ＝ ξ i ∘ ζ i) ＼ H₂ ＞


Code′ : (U V : Factorization f) → Type _
Code′ {f} (X , (ρ₁ , _) , (ι₁ , _) , H₁) (Y , (ρ₂ , _) , (ι₂ , _) , H₂) =
  Σ[ e ꞉ X ≃ Y ]
  Σ[ ζ ꞉ (e .fst ∘ ρ₁ ＝ ρ₂) ]
  Σ[ ξ ꞉ (ι₁ ＝ ι₂ ∘ e .fst) ]
  ＜ H₁ ／ (λ i → f ＝ (ap (_∘ ρ₁) ξ ∙ ap (ι₂ ∘_) ζ) i) ＼ H₂ ＞

convertible
  : (U@(X , (ρ₁ , _) , (ι₁ , _) , H₁) V@(Y , (ρ₂ , _) , (ι₂ , _) , H₂ ) : Factorization f) (e : X ≃ Y)
    (ζ : e .fst ∘ ρ₁ ＝ ρ₂)
    (ξ : ι₁ ＝ ι₂ ∘ e .fst)
  → (H₁ ∙ ap (_∘ ρ₁) ξ ∙ ap (ι₂ ∘_) ζ ＝ H₂)
  → ＜ H₁ ／ (λ i → f ＝ (ap (_∘ ρ₁) ξ ∙ ap (ι₂ ∘_) ζ) i) ＼ H₂ ＞
convertible (X , (ρ₁ , _) , (ι₁ , _) , H₁) (Y , (ρ₂ , _) , (ι₂ , _) , H₂) e ζ ξ p = to-pathP $ subst-path-right _ _ ∙ p

Code : (U V : Factorization f) → Type _
Code (X , (ρ₁ , _) , (ι₁ , _) , H₁) (Y , (ρ₂ , _) , (ι₂ , _) , H₂) =
  Σ[ e ꞉ X ≃ Y ]
  Σ[ ζ ꞉ (e .fst ∘ ρ₁ ＝ ρ₂) ] -- (ι₂ ∘ e .fst) ∘ ρ₁ ＝ ι₂ ∘      ρ₂
  Σ[ ξ ꞉ (ι₁ ＝ ι₂ ∘ e .fst) ] --      ι₁       ∘ ρ₁ ＝ ι₂ ∘ (e .fst ∘ ρ₁)
  (H₁ ∙ ap (_∘ ρ₁) ξ ∙ ap (ι₂ ∘_) ζ ＝ H₂)

open import Foundations.Sigma
open import Foundations.Pi
open import Meta.SIP
open import Functions.Fibration
open import Foundations.Transport
opaque
  @0 code≃path : {f : A → B} → (U V : Factorization f) → Code U V ≃ (U ＝ V)
  code≃path {A} {f} U@(X , (ρ₁ , ρ₁-sur) , (ι₁ , ι₁-emb) , H₁) V@(Y , (ρ₂ , ρ₂-sur) , (ι₂ , ι₂-emb) , H₂) =
    Code U V
      ≃⟨⟩
    Σ[ e ꞉ X ≃ Y ] Σ[ ζ ꞉ (e .fst ∘ ρ₁ ＝ ρ₂) ] Σ[ ξ ꞉ (ι₁ ＝ ι₂ ∘ e .fst) ] (H₁ ∙ ap (_∘ ρ₁) ξ ∙ ap (ι₂ ∘_) ζ ＝ H₂)
      ≃⟨ Σ-ap {!!} {!!} ⟩
    Σ[ q ꞉ (X , ρ₁ , ι₁) ＝ (Y , ρ₂ , ι₂) ] (subst (λ v → f ＝ v .snd .snd ∘ v .snd .fst) q H₁ ＝ H₂)
      ≃⟨ iso→equiv Σ-path-iso ⟩
    ((X , ρ₁ , ι₁) , H₁) ＝ ((Y , ρ₂ , ι₂) , H₂)
      ≃⟨ Σ-prop-path-≃ hlevel! ⟩
    (((X , ρ₁ , ι₁) , H₁) , ρ₁-sur , ι₁-emb) ＝ (((Y , ρ₂ , ι₂) , H₂) , ρ₂-sur , ι₂-emb)
      ≃⟨ ap-≃ {!!} ⟩
    (X , (ρ₁ , ρ₁-sur) , (ι₁ , ι₁-emb) , H₁) ＝ (Y , (ρ₂ , ρ₂-sur) , (ι₂ , ι₂-emb) , H₂)
      ≃⟨⟩
    U ＝ V
      ≃∎

@0 image-factorization-is-unique
  : {A : Type ℓ} {C : Type ℓ′}
  → Π[ f ꞉ (A → C) ] ∃![ B ꞉ Type (ℓ ⊔ ℓ′) ] f factors-through B
image-factorization-is-unique {ℓ} {ℓ′} {A} {C} f = inhabited-prop-is-contr (Im f , image-factorization) $ is-prop-η uniq where
    uniq : (U V : _) → U ＝ V
    uniq (X , (ρ₁ , ρ₁-sur) , (ι₁ , ι₁-emb) , p) (Y , (ρ₂ , ρ₂-sur) , (ι₂ , ι₂-emb) , q) =
      code≃path _ _ .fst $ e , {!!} , {!!} , {!!} where
        -- TODO factor this out?
        helper : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
                 {ρ : A → B} {ι : B → C} → is-surjective ρ → is-embedding ι
               → {c : C} → fibre ι c ≃ ∥ fibre (ι ∘ ρ) c ∥₁
        helper {ρ} {ι} sur emb {c} =
          fibre ι c
            ≃˘⟨ Σ-contract-snd (λ _ → inhabited-prop-is-contr (sur _) hlevel!) ⟩
          Σ[ w ꞉ fibre ι c ] ∥ fibre ρ (w .fst) ∥₁
            ≃⟨ prop-extₑ fib-level hlevel! (λ x → map (x .fst ,_) (x .snd)) (rec fib-level (second ∣_∣₁)) ⟩
          ∥ Σ[ w ꞉ fibre ι c ] fibre ρ (w .fst) ∥₁
            ≃˘⟨ prop-extₑ! (map F.to) (map F.from) ⟩
          ∥ fibre (ι ∘ ρ) c ∥₁ ≃∎
            where
            module F = Equiv fibre-comp
            fib-level = Σ-is-of-hlevel 1 (emb c) hlevel!

        E : Π[ c ꞉ C ] (fibre ι₁ c ≃ fibre ι₂ c)
        E c = fibre ι₁ c              ≃⟨ helper ρ₁-sur ι₁-emb ⟩
              ∥ fibre (ι₁ ∘ ρ₁) c ∥₁  ≃⟨ subst-equiv (λ φ → ∥ fibre φ c ∥₁) (sym p ∙ q) ⟩
              ∥ fibre (ι₂ ∘ ρ₂) c ∥₁  ≃˘⟨ helper ρ₂-sur ι₂-emb ⟩
              fibre ι₂ c              ≃∎

        e : X ≃ Y
        e = X                      ≃⟨ total-equiv ι₁ ⟩
            Σ[ c ꞉ C ] fibre ι₁ c  ≃⟨ Σ-ap-snd E ⟩
            Σ[ c ꞉ C ] fibre ι₂ c  ≃˘⟨ total-equiv ι₂ ⟩
            Y                      ≃∎
