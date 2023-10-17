{-# OPTIONS --safe #-}
module Functions.Fibration where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ ℓᶜ ℓᵉ ℓᵖ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  E : Type ℓᵉ
  y : B
  f : A → B
  g : B → C

Σ-fibre-equiv : (B : A → Type ℓᵇ) (a : A)
              → fibre fst a ≃ B a
Σ-fibre-equiv B a = iso→equiv isom where
  isom : _ ≅ _
  isom .fst ((_ , y) , p) = subst B p y
  isom .snd .is-iso.inv x       = (a , x) , refl
  isom .snd .is-iso.rinv _      = transport-refl _
  isom .snd .is-iso.linv ((_ , y) , p) i =
    (p (~ i) , coe1→i (λ j → B (p (~ i ∧ ~ j))) i y) , λ j → p (~ i ∨ j)

total-equiv : (p : E → B) → E ≃ Σ[ b ꞉ B ] fibre p b
total-equiv p = iso→equiv isom where
  isom : _ ≅ (Σ _ (fibre p))
  isom .fst x                   = p x , x , refl
  isom .snd .is-iso.inv (_ , x , _)    = x
  isom .snd .is-iso.rinv (_ , x , q) i = q i , x , λ j → q (i ∧ j)
  isom .snd .is-iso.linv _             = refl

_/[_]_ : (ℓ : Level) → (Type (ℓ ⊔ ℓ′) → Type ℓ″) → Type ℓ′ → Type (ℓsuc (ℓ ⊔ ℓ′) ⊔ ℓ″ )
_/[_]_ {ℓ′} ℓ P B =
  Σ[ A ꞉ Type (ℓ ⊔ ℓ′) ]
  Σ[ f ꞉ (A → B) ]
  Π[ x ꞉ B ]
  P (fibre f x)

fibre-paths : {z@(a , p) z′@(a′ , p′) : fibre f y}
            → z ＝ z′
            ≃ Σ[ q ꞉ a ＝ a′ ] (sym (ap f q) ∙ p ＝ p′)
fibre-paths {f} {y} {z = a , p} {z′ = a′ , p′} =
  (a , p) ＝ (a′ , p′)                                ≃˘⟨ iso→equiv Σ-path-iso ⟩
  Σ[ q ꞉ a ＝ a′ ] (subst (λ v → f v ＝ y) q p ＝ p′) ≃⟨ Σ-ap-snd (whisker-path-lₑ ∘ subst-path-left p ∘ ap f) ⟩
  Σ[ q ꞉ a ＝ a′ ] (sym (ap f q) ∙ p ＝ p′)           ≃∎

module @0 _ where
  opaque
    unfolding ua
    fibration-equiv : Σ[ E ꞉ Type (level-of-type B ⊔ ℓ) ] (E → B)
                    ≃ (B → Type (level-of-type B ⊔ ℓ))
    fibration-equiv {B} {ℓ} = iso→equiv isom where
      isom : Σ[ E ꞉ Type (level-of-type B ⊔ ℓ) ] (E → B) ≅ (B → Type (level-of-type B ⊔ ℓ))
      isom .fst (E , p)       = fibre p
      isom .snd .is-iso.inv p⁻¹      = Σ _ p⁻¹ , fst
      isom .snd .is-iso.rinv prep i x = ua (Σ-fibre-equiv prep x) i
      isom .snd .is-iso.linv (E , p) i = ua e (~ i) , λ x → fst (ua-unglue e (~ i) x)
        where
        e : E ≃ Σ[ b ꞉ B ] fibre p b
        e = total-equiv p

    map-classifier
      : (P : Type (ℓ ⊔ level-of-type B) → Type ℓᵖ)
      → ℓ /[ P ] B
      ≃ (B → Σ[ T ꞉ Type (ℓ ⊔ level-of-type B) ] P T)
    map-classifier {ℓ} {B} P =
      Σ[ A ꞉ _ ] Σ[ f ꞉ _ ] Π[ x ꞉ B ] P (fibre f x) ≃⟨ Σ-assoc ⟩
      Σ[ (_ , f) ꞉ _ ] Π[ y ꞉ B ] P (fibre f y)      ≃⟨ Σ-ap-fst (fibration-equiv {ℓ = ℓ}) ⟩
      Σ[ A ꞉ _ ] Π[ x ꞉ B ] P (A x)                  ≃˘⟨ Σ-Π-distrib ⟩
      (B → Σ[ T ꞉ _ ] P T)                           ≃∎

  fibre-equality≃fibre-on-paths
    : {z@(_ , p) z′@(_ , p′) : fibre f y}
    → z ＝ z′
    ≃ fibre (ap f) (p ∙ sym p′)
  fibre-equality≃fibre-on-paths = fibre-paths ∙ₑ Σ-ap-snd (λ _ → tiltₑ)

-- ultra fast
fibre-comp : {c : C}
           → fibre (g ∘ f) c
           ≃ Σ[ w ꞉ fibre g c ] fibre f (w .fst)
fibre-comp {g} {f} {c} = iso→equiv $ to , iso from ri li where
  to : fibre (g ∘ f) c → Σ[ w ꞉ fibre g c ] fibre f (w .fst)
  to (a , p) = (f a , p) , a , refl
  from : Σ[ w ꞉ fibre g c ] fibre f (w .fst) → fibre (g ∘ f) c
  from ((c′ , p) , a , q) = a , ap g q ∙ p
  ri : from is-right-inverse-of to
  ri ((c′ , p) , a , q) i =
    (q i , ∙-filler-r (ap g q) p (~ i)) , a , λ j → q (i ∧ j)
  li : from is-left-inverse-of to
  li (a , p) i = a , ∙-filler-r refl p (~ i)
