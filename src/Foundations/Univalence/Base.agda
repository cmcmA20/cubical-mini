{-# OPTIONS --safe #-}
module Foundations.Univalence.Base where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.FromPath
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
      (φ = i1) → u i  1=1 , line→Equiv (λ j → u (i ∧ ~ j) 1=1)
      (i = i0) → u i0 1=1 , line→Equiv (λ i → u i0        1=1)

  hcomp＝Glue : {φ : _} (u : ∀ i → Partial (φ ∨ ~ i) (Type ℓ))
              →  hcomp φ u
              ＝ Glue (u i0 1=1)
                      (λ { (φ = i1) → u i1 1=1 , line→Equiv (λ j → u (~ j) 1=1) })
  hcomp＝Glue {φ} u = hcomp-unique φ u (glue-hfill φ u)


@0 ua : A ≃ B → A ＝ B
ua {A} {B} e i = Glue B λ where
  (i = i0) → A , e
  (i = i1) → B , idₑ

@0 Iso→Path : Iso A B → A ＝ B
Iso→Path (f , r) = ua (f , is-iso→is-equiv r)

@0 ua-unglue : (e : A ≃ B) (i : I) (x : ua e i) → B
ua-unglue e i x = unglue (i ∨ ~ i) x

@0 ua-PathP→path : (e : A ≃ B) {x : A} {y : B}
                 → ＜ x ／ (λ i → ua e i) ＼ y ＞
                 → e .fst x ＝ y
ua-PathP→path e p i = ua-unglue e i (p i)

@0 ua-glue : (e : A ≃ B) (i : I)
             (x : Partial (~ i) A)
             (y : B [ _ ↦ (λ { (i = i0) → e .fst (x 1=1) }) ])
           → ua e i [ _ ↦ (λ { (i = i0) → x 1=1
                             ; (i = i1) → outS y
                             }) ]
ua-glue e i x y = inS (glue {φ = i ∨ ~ i}
                                 (λ { (i = i0) → x 1=1
                                    ; (i = i1) → outS y })
                                 (outS y))

@0 path→ua-PathP : (e : A ≃ B) {x : A} {y : B}
                 → e .fst x ＝ y
                 → ＜ x ／ (λ i → ua e i) ＼ y ＞
path→ua-PathP e {x} p i = outS (ua-glue e i (λ { (i = i0) → x }) (inS (p i)))

@0 ua-PathP≃path : (e : A ≃ B) {x : A} {y : B}
                 → (e .fst x ＝ y) ≃ ＜ x ／ (λ i → ua e i) ＼ y ＞
ua-PathP≃path eqv .fst = path→ua-PathP eqv
ua-PathP≃path eqv .snd .equiv-proof y .fst = strict-contr-fibres (ua-PathP→path eqv) y .fst
ua-PathP≃path eqv .snd .equiv-proof y .snd = strict-contr-fibres (ua-PathP→path eqv) y .snd

path→Equiv : A ＝ B → A ≃ B
path→Equiv p = line→Equiv (λ i → p i)

path→Equiv-refl : path→Equiv (refl {x = A}) ＝ idₑ
path→Equiv-refl {A} = Σ-path (λ i x → coe1→i (λ i → A) i x)
                             (is-prop→PathP (λ i → is-equiv-is-prop _) _ _)

@0 ua-id-Equiv : ua idₑ ＝ refl {x = A}
ua-id-Equiv {A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idₑ)

ua-β : (e : A ≃ B) (x : A) → transport (ua e) x ＝ e .fst x
ua-β {A} {B} e x i = coe1→i (λ _ → B) i (e .fst x)

@0 ua-η : (P : A ＝ B) → ua (path→Equiv P) ＝ P
ua-η = J (λ _ q → ua (path→Equiv q) ＝ q) (cong ua path→Equiv-refl ∙ ua-id-Equiv)

@0 Path≅Equiv : Iso (A ＝ B) (A ≃ B)
Path≅Equiv = path→Equiv , r where
  r : is-iso path→Equiv
  r .is-iso.inv = ua
  r .is-iso.rinv (f , is-eqv) = Σ-path (fun-ext (ua-β (f , is-eqv)))
                                       (is-equiv-is-prop f _ _)
  r .is-iso.linv = J (λ _ p → ua (path→Equiv p) ＝ p)
                     (ap ua path→Equiv-refl ∙ ua-id-Equiv)

@0 univalence : is-equiv (path→Equiv {A = A} {B = B})
univalence = is-iso→is-equiv (Path≅Equiv .snd)

@0 univalence⁻¹ : is-equiv (ua {A = A} {B = B})
univalence⁻¹ = is-iso→is-equiv (is-iso-inv (Path≅Equiv .snd))

@0 Equiv-is-contr : (A : Type ℓ) → is-contr (Σ[ B ꞉ Type ℓ ] (A ≃ B))
Equiv-is-contr A .fst             = A , idₑ
Equiv-is-contr A .snd (B , A≃B) i = ua A≃B i , p i , q i where
  p : ＜ id ／ (λ i → A → ua A≃B i) ＼ A≃B .fst ＞
  p i x = outS (ua-glue A≃B i (λ { (i = i0) → x }) (inS (A≃B .fst x)))

  q : ＜ id-is-equiv ／ (λ i → is-equiv (p i)) ＼ A≃B .snd ＞
  q = is-prop→PathP (λ i → is-equiv-is-prop (p i)) _ _

@0 Equiv-J : (P : (B : Type ℓ) → A ≃ B → Type ℓ′)
           → P A idₑ
           → {B : Type ℓ} (e : A ≃ B)
           → P B e
Equiv-J P pid eqv =
  subst (λ e → P (e .fst) (e .snd)) (Equiv-is-contr _ .snd (_ , eqv)) pid

@0 ap-is-equiv : {A B : Type ℓ}
                 (f : A → B) → is-equiv f
               → {x y : A}
               → is-equiv (ap {x = x} {y = y} f)
ap-is-equiv f eqv =
  Equiv-J (λ B e → is-equiv (ap (e .fst))) id-is-equiv (f , eqv)
