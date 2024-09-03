{-# OPTIONS --safe #-}
module Foundations.Univalence where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.HLevel.Base
open import Foundations.Isomorphism

private variable
  ℓ ℓ′ ℓ″ : Level
  A B E : Type ℓ

module @0 _ where private
  glue-hfill : (φ : _) (u : ∀ i → Partial (φ ∨ ~ i) (Type ℓ))
               (i : I)
             → Type ℓ [ _ ↦ (λ { (i = i0) → u i0 1=1
                               ; (φ = i1) → u i 1=1 }) ]
  glue-hfill φ u i = inS $ₛ
    Glue (u i0 1=1) {φ = φ ∨ ~ i} λ where
      (φ = i1) → u i  1=1 , line→≃ (λ j → u (i ∧ ~ j) 1=1)
      (i = i0) → u i0 1=1 , line→≃ (λ i → u i0        1=1)

  hcomp=Glue : {φ : _} (u : ∀ i → Partial (φ ∨ ~ i) (Type ℓ))
             →  hcomp φ u
             ＝ Glue (u i0 1=1)
                     (λ { (φ = i1) → u i1 1=1 , line→≃ (λ j → u (~ j) 1=1) })
  hcomp=Glue {φ} u = hcomp-unique φ u (glue-hfill φ u)


module @0 _ where opaque
  ua : A ≃ B → A ＝ B
  ua {A} {B} e i = Glue B λ where
    (i = i0) → A , e
    (i = i1) → B , refl

  ua-unglue : (e : A ≃ B) (i : I) (x : ua e i) → B
  ua-unglue e i x = unglue (i ∨ ~ i) x

  ua-pathᴾ→= : (e : A ≃ B) {x : A} {y : B}
             → ＜ x ／ (λ i → ua e i) ＼ y ＞
             → e # x ＝ y
  ua-pathᴾ→= e p i = ua-unglue e i (p i)

  ua-glue : (e : A ≃ B) (i : I)
            (x : Partial (~ i) A)
            (y : B [ _ ↦ (λ { (i = i0) → e # (x 1=1) }) ])
          → ua e i [ _ ↦ (λ { (i = i0) → x 1=1
                            ; (i = i1) → outS y
                            }) ]
  ua-glue e i x y = inS (glue {φ = i ∨ ~ i}
                                   (λ { (i = i0) → x 1=1
                                      ; (i = i1) → outS y })
                                   (outS y))

  =→ua-pathᴾ : (e : A ≃ B) {x : A} {y : B}
             → e # x ＝ y
             → ＜ x ／ (λ i → ua e i) ＼ y ＞
  =→ua-pathᴾ e {x} p i = outS (ua-glue e i (λ { (i = i0) → x }) (inS (p i)))

  ua-pathᴾ≃= : (e : A ≃ B) {x : A} {y : B}
             → (e # x ＝ y) ≃ ＜ x ／ (λ i → ua e i) ＼ y ＞
  ua-pathᴾ≃= eqv .fst = =→ua-pathᴾ eqv
  ua-pathᴾ≃= eqv .snd .equiv-proof y .fst = strict-contr-fibres (ua-pathᴾ→= eqv) y .fst
  ua-pathᴾ≃= eqv .snd .equiv-proof y .snd = strict-contr-fibres (ua-pathᴾ→= eqv) y .snd

  ua→
    : {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ′}
      {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
    → Π[ a ꞉ A₀ ] ＜ f₀ a ／ B ＼ f₁ (e # a) ＞
    → ＜ f₀ ／ (λ i → ua e i → B i) ＼ f₁ ＞
  ua→ {B} {f₀} {f₁} h i a = comp (λ j → B (i ∨ ~ j)) (∂ i) λ where
    j (j = i0) → f₁ (unglue (∂ i) a)
    j (i = i0) → h a (~ j)
    j (i = i1) → f₁ a

@0 ≅→= : A ≅ B → A ＝ B
≅→= = ≅→≃ ∙ ua

=→≃ : A ＝ B → A ≃ B
=→≃ p = line→≃ (λ i → p i)

=→≃-refl : =→≃ (refl {x = A}) ＝ refl
=→≃-refl = equiv-ext $ fun-ext transport-refl

opaque
  unfolding ua
  @0 ua-idₑ : ua refl ＝ refl {x = A}
  ua-idₑ {A} i j = Glue A {φ = i ∨ ∂ j} (λ _ → A , refl)

  ua-β : (e : A ≃ B) (x : A) → transport (ua e) x ＝ e # x
  ua-β e x = transport-refl _

  @0 ua-η : (p : A ＝ B) → ua (=→≃ p) ＝ p
  ua-η {A} {B} p i j = Glue B ω where
    ω : Partial (i ∨ ∂ j) (Σ[ T ꞉ Type (level-of-type B) ] (T ≃ B))
    ω (i = i1) = p j , transport-line-equiv (λ k → p k) j
    ω (j = i0) = A   , =→≃ p
    ω (j = i1) = B   , refl

module @0 _ where
  open Iso

  path≅equiv : (A ＝ B) ≅ (A ≃ B)
  path≅equiv {A} {B} = iso =→≃ ua (fun-ext $ equiv-ext ∘ fun-ext ∘ ua-β) (fun-ext ua-η)

  univalence : is-equiv (=→≃ {A = A} {B = B})
  univalence = is-inv→is-equiv (make-invertible _ (path≅equiv .inverses))

  univalence⁻¹ : is-equiv (ua {A = A} {B = B})
  univalence⁻¹ = is-inv→is-equiv (is-invertible.op (make-invertible _ (path≅equiv .inverses)))

  opaque
    unfolding ua
    equiv-is-contr : (A : Type ℓ) → is-contr (Σ[ B ꞉ Type ℓ ] (A ≃ B))
    equiv-is-contr A .fst             = A , refl
    equiv-is-contr A .snd (B , A≃B) i = ua A≃B i , p i , q i where
      p : ＜ id ／ (λ i → A → ua A≃B i) ＼ A≃B .fst ＞
      p i x = outS (ua-glue A≃B i (λ { (i = i0) → x }) (inS (A≃B # x)))

      q : ＜ id-is-equiv ／ (λ i → is-equiv (p i)) ＼ A≃B .snd ＞
      q = is-prop→pathᴾ (λ i → is-equiv-is-prop (p i)) _ _

    Jₑ : (P : (B : Type ℓ) → A ≃ B → Type ℓ′)
       → P A refl
       → {B : Type ℓ} (e : A ≃ B)
       → P B e
    Jₑ P pid eqv =
      subst (λ e → P (e .fst) (e .snd)) (equiv-is-contr _ .snd (_ , eqv)) pid

    unglue-is-equiv
      : {A : Type ℓ}
        (φ : I)
      → {B : Partial φ (Σ[ X ꞉ Type ℓ′ ] (X ≃ A))}
      → is-equiv {A = Glue A B} (unglue φ)
    unglue-is-equiv {A} φ {B} .equiv-proof y = extend→is-contr ctr where
      module _ (ψ : I) (par : Partial ψ (fibre (unglue φ) y)) where
        fib : .(p : IsOne φ)
            → fibre (B p .snd .fst) y
              [ (ψ ∧ φ) ↦ (λ { (ψ = i1) (φ = i1) → par 1=1 }) ]
        fib p = is-contr→extend (B p .snd .snd .equiv-proof y) (ψ ∧ φ) _

        sys : ∀ j → Partial (φ ∨ ψ ∨ ~ j) A
        sys j (j = i0) = y
        sys j (φ = i1) = outS (fib 1=1) .snd (~ j)
        sys j (ψ = i1) = par 1=1 .snd (~ j)

        ctr : Σ _ _ [ _ ↦ _ ]
        ctr = inS $ₛ glue-inc φ {Tf = B} (λ { (φ = i1) → outS (fib 1=1) .fst })
                      (inS (hcomp (φ ∨ ψ) sys))
                   , (λ i → hfill (φ ∨ ψ) (~ i) sys)

@0 ap-is-equiv : {A B : Type ℓ}
                 (f : A → B) → is-equiv f
               → {x y : A}
               → is-equiv (ap {x = x} {y = y} f)
ap-is-equiv f eqv = Jₑ (λ B e → is-equiv (ap$ e)) id-is-equiv (f , eqv)

@0 ap-≃ : {A B : Type ℓ} {x y : A} (e : A ≃ B) → (x ＝ y) ≃ (e # x ＝ e # y)
ap-≃ e = ap _ , ap-is-equiv _ (e .snd)

-- TODO worth fixing?
-- opaque
--   unfolding ua ua-unglue
--   @0 ua-unglue-is-equiv
--     : (f : A ≃ B)
--     → ＜ f .snd ／ (λ i → is-equiv (ua-unglue f i)) ＼ id-is-equiv ＞
--   ua-unglue-is-equiv f =
--     is-prop→pathP (λ j → is-equiv-is-prop (ua-unglue f j)) (f .snd) id-is-equiv
