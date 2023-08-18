{-# OPTIONS --safe #-}
module Functions.Embedding where

open import Foundations.Base
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Search.HLevel

open import Structures.n-Type

open import Data.Unit.Instances.HLevel

open import Functions.Equiv.Fibrewise

private variable
  ℓ ℓ′ ℓ″ : Level
  A E : Type ℓ
  B : Type ℓ′
  f : A → B

Injective : (A → B) → Type _
Injective f = ∀ {x y} → f x ＝ f y → x ＝ y

_↣_ : Type ℓ → Type ℓ′ → Type _
A ↣ B = Σ[ f ꞉ (A → B) ] Injective f

injective→has-prop-fibres
  : is-set B → (f : A → B) → Injective f
  → ∀ x → is-prop (fibre f x)
injective→has-prop-fibres B-set f inj x = is-prop-η λ (f*x , p) (f*x′ , q) →
  Σ-prop-path! (inj (p ∙ sym q))
  where instance _ = B-set

has-prop-fibres→injective
  : (f : A → B) → (∀ x → is-prop (fibre f x))
  → Injective f
has-prop-fibres→injective _ prop p = ap fst (is-prop-β (prop _) (_ , p) (_ , refl))

between-sets-injective≃has-prop-fibres
  : is-set A → is-set B → (f : A → B)
  → Injective f ≃ (∀ x → is-prop (fibre f x))
between-sets-injective≃has-prop-fibres A-set B-set f =
  prop-extₑ! (injective→has-prop-fibres B-set f)
             (has-prop-fibres→injective f)
  where instance _ = A-set

is-embedding : (A → B) → Type _
is-embedding f = ∀ x → is-prop (fibre f x)

_↪_ : Type ℓ → Type ℓ′ → Type _
A ↪ B = Σ[ f ꞉ (A → B) ] is-embedding f


fibre-equiv : (B : A → Type ℓ′) (a : A)
            → fibre fst a ≃ B a
fibre-equiv B a = iso→equiv isom where
  isom : Iso _ _
  isom .fst ((x , y) , p) = subst B p y
  isom .snd .is-iso.inv x        = (a , x) , refl
  isom .snd .is-iso.rinv x i     = coe1→i (λ _ → B a) i x
  isom .snd .is-iso.linv ((x , y) , p) i =
    (p (~ i) , coe1→i (λ j → B (p (~ i ∧ ~ j))) i y) , λ j → p (~ i ∨ j)

total-equiv : (p : E → B) → E ≃ Σ B (fibre p)
total-equiv p = iso→equiv isom where
  isom : Iso _ (Σ _ (fibre p))
  isom .fst x                   = p x , x , refl
  isom .snd .is-iso.inv (_ , x , _)    = x
  isom .snd .is-iso.rinv (b , x , q) i = q i , x , λ j → q (i ∧ j)
  isom .snd .is-iso.linv x             = refl

opaque
  unfolding ua
  @0 fibration-equiv : ∀ {B : Type ℓ}
                     → (Σ[ E ꞉ Type (ℓ ⊔ ℓ′) ] (E → B))
                     ≃ (B → Type (ℓ ⊔ ℓ′))
  fibration-equiv {B} = iso→equiv isom where
    isom : Iso (Σ[ E ꞉ Type _ ] (E → B)) (B → Type _)
    isom .fst (E , p)       = fibre p
    isom .snd .is-iso.inv p⁻¹      = Σ _ p⁻¹ , fst
    isom .snd .is-iso.rinv prep i x = ua (fibre-equiv prep x) i
    isom .snd .is-iso.linv (E , p) i = ua e (~ i) , λ x → fst (ua-unglue e (~ i) x)
      where e : _ ≃ _ ; e = total-equiv p

_/[_]_ : (ℓ : Level) → (Type (ℓ ⊔ ℓ′) → Type ℓ″) → Type ℓ′ → Type _
_/[_]_ {ℓ′} ℓ P B =
  Σ[ A ꞉ Type (ℓ ⊔ ℓ′) ]
  Σ[ f ꞉ (A → B) ]
  Π[ x ꞉ B ]
  P (fibre f x)

opaque
  unfolding fibration-equiv
  @0 map-classifier
    : {ℓ : Level} {B : Type ℓ′} (P : Type (ℓ ⊔ ℓ′) → Type ℓ″)
    → ℓ /[ P ] B
    ≃ (B → Σ[ T ꞉ _ ] P T)
  map-classifier {ℓ′} {ℓ} {B} P =
    (Σ[ A ꞉ _ ] Σ[ f ꞉ _ ] Π[ x ꞉ B ] P (fibre f x)) ≃⟨ Σ-assoc ⟩
    (Σ[ (_ , f) ꞉ _ ] Π[ y ꞉ B ] P (fibre f y))      ≃⟨ Σ-ap-fst (fibration-equiv {ℓ′} {ℓ}) ⟩
    (Σ[ A ꞉ _ ] Π[ x ꞉ B ] P (A x))                  ≃⟨ Σ-Π-distrib ₑ⁻¹ ⟩
    (B → Σ[ T ꞉ _ ] P T)                             ≃∎

@0 subtype-classifier
  : {B : Type ℓ}
  → Σ[ A ꞉ Type ℓ ] A ↪ B
  ≃ (B → Σ[ T ꞉ Type ℓ ] is-prop T)
subtype-classifier {ℓ} = map-classifier {ℓ = ℓ} is-prop

module @0 subtype-classifier {ℓ} {B : Type ℓ} = Equiv (subtype-classifier {B = B})


subset-proj-embedding
  : {B : A → Type ℓ}
  → (∀ x → is-prop (B x))
  → is-embedding {A = Σ A B} fst
subset-proj-embedding {B} B-prop x = is-of-hlevel-≃ 1 (fibre-equiv B x) (B-prop _)

embedding→monic
  : {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-embedding f
  → ∀ {C : Type ℓ″} (g h : C → A) → f ∘ g ＝ f ∘ h → g ＝ h
embedding→monic {f} emb g h p =
  fun-ext λ x → ap fst (is-prop-β (emb _) (g x , refl) (h x , happly (sym p) x))

monic→is-embedding
  : {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-set B
  → (∀ {C : Set ℓ″} (g h : ⌞ C ⌟ → A) → f ∘ g ＝ f ∘ h → g ＝ h)
  → is-embedding f
monic→is-embedding {f} B-set monic =
  injective→has-prop-fibres B-set _ λ {x} {y} p →
    happly (monic {C = el! $ Lift _ ⊤} (λ _ → x) (λ _ → y) (fun-ext (λ _ → p))) _


embedding-lemma : (∀ x → is-contr (fibre f (f x))) → is-embedding f
embedding-lemma {f} cffx y = is-prop-η λ (x , p) q →
  is-prop-β (is-contr→is-prop (subst is-contr (ap (fibre f) p) (cffx x))) (x , p) q

cancellable→embedding : (∀ {x y} → (f x ＝ f y) ≃ (x ＝ y)) → is-embedding f
cancellable→embedding eqv =
  embedding-lemma λ x → is-of-hlevel-≃ 0 (Σ-ap-snd (λ _ → eqv)) $
    is-contr-η $ (x , refl) , λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

is-embedding→cancellable : is-embedding f → ∀ {x y} → is-equiv {B = f x ＝ f y} (ap f)
is-embedding→cancellable {f} emb = total→is-equiv {f = λ y p → ap {y = y} f p}
  (is-contr→is-equiv
    (is-contr-η $ (_ , refl) , λ (y , p) i → p i , λ j → p (i ∧ j))
    (is-contr-η $ (_ , refl) , is-prop-β (is-of-hlevel-≃ 1 (Σ-ap-snd (λ _ → sym-equiv)) (emb _)) _))


is-embedding→is-of-hlevel
  : ∀ n → {f : A → B} → is-embedding f
  → is-of-hlevel (suc n) B
  → is-of-hlevel (suc n) A
is-embedding→is-of-hlevel n {f} emb a-hl = is-of-hlevel-≃ (suc n) (total-equiv f) $
  Σ-is-of-hlevel (suc n) a-hl λ x → is-prop→is-of-hlevel-suc (emb x)

is-equiv→is-embedding : is-equiv f → is-embedding f
is-equiv→is-embedding r y = is-contr→is-prop $ is-contr-η $ r .equiv-proof y

equiv→embedding : A ≃ B → A ↪ B
equiv→embedding (f , p) = f , is-equiv→is-embedding p
