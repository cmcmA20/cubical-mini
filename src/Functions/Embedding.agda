{-# OPTIONS --safe #-}
module Functions.Embedding where

open import Foundations.Base
open import Foundations.Univalence
open import Foundations.HLevel
open import Foundations.Sigma
open import Functions.Equiv.Fibrewise
open import Structures.n-Type

private variable
  ℓ ℓ′ ℓ″ : Level
  A B E : Type ℓ
  w x : A

injective : (A → B) → Type _
injective f = ∀ {x y} → f x ＝ f y → x ＝ y

injective→has-prop-fibres
  : is-set B → (f : A → B) → injective f
  → ∀ x → is-prop (fibre f x)
injective→has-prop-fibres bset f inj x (f*x , p) (f*x′ , q) =
  Σ-prop-path (λ x → bset _ _) (inj (p ∙ sym q))

has-prop-fibres→injective
  : (f : A → B) → (∀ x → is-prop (fibre f x))
  → injective f
has-prop-fibres→injective _ prop p = ap fst (prop _ (_ , p) (_ , refl))

between-sets-injective≃has-prop-fibres
  : is-set A → is-set B → (f : A → B)
  → injective f ≃ (∀ x → is-prop (fibre f x))
between-sets-injective≃has-prop-fibres A-set B-set f =
  prop-extₑ (λ p q i x → A-set _ _ (p x) (q x) i)
            (Π-is-of-hlevel 1 λ _ → is-prop-is-prop)
            (injective→has-prop-fibres B-set f)
            (has-prop-fibres→injective f)

is-embedding : (A → B) → Type _
is-embedding f = ∀ x → is-prop (fibre f x)

_↪_ : Type ℓ → Type ℓ′ → Type _
A ↪ B = Σ[ f ꞉ (A → B) ] is-embedding f


Fibre-Equiv : (B : A → Type ℓ′) (a : A)
            → fibre fst a ≃ B a
Fibre-Equiv B a = Iso→Equiv isom where
  isom : Iso _ _
  isom .fst ((x , y) , p) = subst B p y
  isom .snd .is-iso.inv x        = (a , x) , refl
  isom .snd .is-iso.rinv x i     = coe1→i (λ _ → B a) i x
  isom .snd .is-iso.linv ((x , y) , p) i =
    (p (~ i) , coe1→i (λ j → B (p (~ i ∧ ~ j))) i y) , λ j → p (~ i ∨ j)

Total-Equiv : (p : E → B) → E ≃ Σ B (fibre p)
Total-Equiv p = Iso→Equiv isom where
  isom : Iso _ (Σ _ (fibre p))
  isom .fst x                   = p x , x , refl
  isom .snd .is-iso.inv (_ , x , _)    = x
  isom .snd .is-iso.rinv (b , x , q) i = q i , x , λ j → q (i ∧ j)
  isom .snd .is-iso.linv x             = refl

@0 Fibration-Equiv : ∀ {B : Type ℓ}
                   → (Σ[ E ꞉ Type (ℓ ⊔ ℓ′) ] (E → B))
                   ≃ (B → Type (ℓ ⊔ ℓ′))
Fibration-Equiv {B} = Iso→Equiv isom where
  isom : Iso (Σ[ E ꞉ Type _ ] (E → B)) (B → Type _)
  isom .fst (E , p)       = fibre p
  isom .snd .is-iso.inv p⁻¹      = Σ _ p⁻¹ , fst
  isom .snd .is-iso.rinv prep i x = ua (Fibre-Equiv prep x) i
  isom .snd .is-iso.linv (E , p) i = ua e (~ i) , λ x → fst (ua-unglue e (~ i) x)
    where e = Total-Equiv p

_/[_]_ : (ℓ : Level) → (Type (ℓ ⊔ ℓ′) → Type ℓ″) → Type ℓ′ → Type _
_/[_]_ {ℓ′} ℓ P B =
  Σ[ A ꞉ Type (ℓ ⊔ ℓ′) ]
  Σ[ f ꞉ (A → B) ]
  Π[ x ꞉ B ]
  P (fibre f x)

@0 Map-classifier
  : {ℓ : Level} {B : Type ℓ′} (P : Type (ℓ ⊔ ℓ′) → Type ℓ″)
  → ℓ /[ P ] B
  ≃ (B → Σ[ T ꞉ _ ] P T)
Map-classifier {ℓ′} {ℓ} {B} P =
  (Σ[ A ꞉ _ ] Σ[ f ꞉ _ ] Π[ x ꞉ B ] P (fibre f x)) ≃⟨ Σ-assoc ⟩
  (Σ[ (_ , f) ꞉ _ ] Π[ y ꞉ B ] P (fibre f y))      ≃⟨ Σ-ap-fst (Fibration-Equiv {ℓ′} {ℓ}) ⟩
  (Σ[ A ꞉ _ ] Π[ x ꞉ B ] P (A x))                  ≃⟨ Σ-Π-distrib ₑ⁻¹ ⟩
  (B → Σ[ T ꞉ _ ] P T)                             ≃∎

@0 subtype-classifier
  : {B : Type ℓ}
  → (Σ[ A ꞉ Type ℓ ] (A ↪ B))
  ≃ (B → Σ[ T ꞉ Type ℓ ] (is-prop T))
subtype-classifier {ℓ} = Map-classifier {ℓ = ℓ} is-prop

module @0 subtype-classifier {ℓ} {B : Type ℓ} = Equiv (subtype-classifier {B = B})

Subset-proj-embedding
  : ∀ {B : A → Type ℓ} → (∀ x → is-prop (B x))
  → is-embedding {A = Σ A B} fst
Subset-proj-embedding {B = B} B-prop x = is-of-hlevel-≃ 1 (Fibre-Equiv B x) (B-prop _)

embedding→monic
  : {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-embedding f
  → ∀ {C : Type ℓ″} (g h : C → A) → f ∘ g ＝ f ∘ h → g ＝ h
embedding→monic {f = f} emb g h p =
  fun-ext λ x → ap fst (emb _ (g x , refl) (h x , happly (sym p) x))

monic→is-embedding
  : {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-set B
  → (∀ {C : Set ℓ″} (g h : ⌞ C ⌟ → A) → f ∘ g ＝ f ∘ h → g ＝ h)
  → is-embedding f
monic→is-embedding {f} bset monic =
  injective→has-prop-fibres bset _ λ {x} {y} p →
    happly (monic {C = el (Lift _ ⊤) (λ _ _ _ _ i j → lift tt)} (λ _ → x) (λ _ → y) (fun-ext (λ _ → p))) _

module _ {A : Type ℓ} {B : Type ℓ′} {f : A → B} where
  embedding-lemma : (∀ x → is-contr (fibre f (f x))) → is-embedding f
  embedding-lemma cffx y (x , p) q =
    is-contr→is-prop (subst is-contr (ap (fibre f) p) (cffx x)) (x , p) q

  cancellable→embedding : (∀ {x y} → (f x ＝ f y) ≃ (x ＝ y)) → is-embedding f
  cancellable→embedding eqv =
    embedding-lemma λ x → is-of-hlevel-≃ 0 (Σ-ap-snd (λ _ → eqv)) $
      (x , refl) , λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

  embedding→cancellable : is-embedding f → ∀ {x y} → is-equiv {B = f x ＝ f y} (ap f)
  embedding→cancellable emb = total→equiv {f = λ y p → ap {y = y} f p}
    (is-contr→is-equiv
      ((_ , refl) , λ (y , p) i → p i , λ j → p (i ∧ j))
      ((_ , refl) , (is-of-hlevel-≃ 1 (Σ-ap-snd λ _ → sym-Equiv) (emb _) _)))

  abstract
    embedding→is-hlevel
      : ∀ n → is-embedding f
      → is-of-hlevel (suc n) B
      → is-of-hlevel (suc n) A
    embedding→is-hlevel n emb a-hl = is-of-hlevel-≃ (suc n) (Total-Equiv f) $
      Σ-is-of-hlevel (suc n) a-hl λ x → is-prop→is-hlevel-suc (emb x)
