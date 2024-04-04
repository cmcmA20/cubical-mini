{-# OPTIONS --safe #-}
module Foundations.Univalence.Base where

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

  hcomp＝Glue : {φ : _} (u : ∀ i → Partial (φ ∨ ~ i) (Type ℓ))
              →  hcomp φ u
              ＝ Glue (u i0 1=1)
                      (λ { (φ = i1) → u i1 1=1 , line→≃ (λ j → u (~ j) 1=1) })
  hcomp＝Glue {φ} u = hcomp-unique φ u (glue-hfill φ u)


module @0 _ where opaque
  ua : A ≃ B → A ＝ B
  ua {A} {B} e i = Glue B λ where
    (i = i0) → A , e
    (i = i1) → B , idₑ

  ua-unglue : (e : A ≃ B) (i : I) (x : ua e i) → B
  ua-unglue e i x = unglue (i ∨ ~ i) x

  ua-pathP→＝ : (e : A ≃ B) {x : A} {y : B}
                → ＜ x ／ (λ i → ua e i) ＼ y ＞
                → e .fst x ＝ y
  ua-pathP→＝ e p i = ua-unglue e i (p i)

  ua-glue : (e : A ≃ B) (i : I)
            (x : Partial (~ i) A)
            (y : B [ _ ↦ (λ { (i = i0) → e .fst (x 1=1) }) ])
          → ua e i [ _ ↦ (λ { (i = i0) → x 1=1
                            ; (i = i1) → outS y
                            }) ]
  ua-glue e i x y = inS (glue {φ = i ∨ ~ i}
                                   (λ { (i = i0) → x 1=1
                                      ; (i = i1) → outS y })
                                   (outS y))

  ＝→ua-pathP : (e : A ≃ B) {x : A} {y : B}
              → e .fst x ＝ y
              → ＜ x ／ (λ i → ua e i) ＼ y ＞
  ＝→ua-pathP e {x} p i = outS (ua-glue e i (λ { (i = i0) → x }) (inS (p i)))

  ua-pathP≃＝ : (e : A ≃ B) {x : A} {y : B}
              → (e .fst x ＝ y) ≃ ＜ x ／ (λ i → ua e i) ＼ y ＞
  ua-pathP≃＝ eqv .fst = ＝→ua-pathP eqv
  ua-pathP≃＝ eqv .snd .equiv-proof y .fst = strict-contr-fibres (ua-pathP→＝ eqv) y .fst
  ua-pathP≃＝ eqv .snd .equiv-proof y .snd = strict-contr-fibres (ua-pathP→＝ eqv) y .snd

@0 iso→＝ : Iso A B → A ＝ B
iso→＝ (f , r) = ua (f , is-iso→is-equiv r)

@0 iso→path : _
iso→path = iso→＝
{-# WARNING_ON_USAGE iso→path "Use `iso→＝`" #-}

＝→≃ : A ＝ B → A ≃ B
＝→≃ p = line→≃ (λ i → p i)

path→equiv = ＝→≃
{-# WARNING_ON_USAGE path→equiv "Use `＝→≃`" #-}

＝→≃-refl : ＝→≃ (refl {x = A}) ＝ idₑ
＝→≃-refl = equiv-ext $ fun-ext transport-refl

opaque
  unfolding ua transport-line-is-equiv
  @0 ua-idₑ : ua idₑ ＝ refl {x = A}
  ua-idₑ {A} i j = Glue A {φ = i ∨ ∂ j} (λ _ → A , idₑ)

  ua-β : (e : A ≃ B) (x : A) → transport (ua e) x ＝ e .fst x
  ua-β e x = transport-refl _

  @0 ua-η : (p : A ＝ B) → ua (＝→≃ p) ＝ p
  ua-η {A} {B} p i j = Glue B ω where
    ω : Partial (i ∨ ∂ j) (Σ[ T ꞉ Type (level-of-type B) ] (T ≃ B))
    ω (i = i1) = p j , transport-line-equiv (λ k → p k) j
    ω (j = i0) = A   , ＝→≃ p
    ω (j = i1) = B   , idₑ

module @0 _ where opaque
  unfolding is-of-hlevel ua
  path≅equiv : (A ＝ B) ≅ (A ≃ B)
  path≅equiv {A} {B} = ＝→≃ , r where
    r : is-iso {A = A ＝ B} ＝→≃
    r .is-iso.inv  = ua
    r .is-iso.rinv = equiv-ext ∘ fun-ext ∘ ua-β
    r .is-iso.linv = ua-η

  univalence : is-equiv (＝→≃ {A = A} {B = B})
  univalence = is-iso→is-equiv (path≅equiv .snd)

  univalence⁻¹ : is-equiv (ua {A = A} {B = B})
  univalence⁻¹ = is-iso→is-equiv (is-iso-inv (path≅equiv .snd))

  equiv-is-contr : (A : Type ℓ) → is-contr (Σ[ B ꞉ Type ℓ ] (A ≃ B))
  equiv-is-contr A .fst             = A , idₑ
  equiv-is-contr A .snd (B , A≃B) i = ua A≃B i , p i , q i where
    p : ＜ id ／ (λ i → A → ua A≃B i) ＼ A≃B .fst ＞
    p i x = outS (ua-glue A≃B i (λ { (i = i0) → x }) (inS (A≃B .fst x)))

    q : ＜ id-is-equiv ／ (λ i → is-equiv (p i)) ＼ A≃B .snd ＞
    q = is-prop→pathP (λ i → is-equiv-is-prop (p i)) _ _

  Jₑ : (P : (B : Type ℓ) → A ≃ B → Type ℓ′)
     → P A idₑ
     → {B : Type ℓ} (e : A ≃ B)
     → P B e
  Jₑ P pid eqv =
    subst (λ e → P (e .fst) (e .snd)) (equiv-is-contr _ .snd (_ , eqv)) pid

  unglue-is-equiv
    : (φ : I)
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
ap-is-equiv f eqv = Jₑ (λ B e → is-equiv (ap (e .fst))) id-is-equiv (f , eqv)

@0 ap-≃ : {A B : Type ℓ} {x y : A} (e : A ≃ B) → (x ＝ y) ≃ (e .fst x ＝ e .fst y)
ap-≃ e = ap _ , ap-is-equiv _ (e .snd)

-- TODO worth fixing?
-- opaque
--   unfolding ua ua-unglue
--   @0 ua-unglue-is-equiv
--     : (f : A ≃ B)
--     → ＜ f .snd ／ (λ i → is-equiv (ua-unglue f i)) ＼ id-is-equiv ＞
--   ua-unglue-is-equiv f =
--     is-prop→pathP (λ j → is-equiv-is-prop (ua-unglue f j)) (f .snd) id-is-equiv
