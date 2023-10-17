{-# OPTIONS --safe #-}
module Foundations.Sigma.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Transport

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  A′ : Type ℓ′
  B P : A → Type ℓ″
  Q : A → Type ℓ‴

-- Unique existence

∃! : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃! A B = is-contr (Σ[ a ꞉ A ] B a)

infixr 6 ∃!-syntax
∃!-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃!-syntax = ∃!

syntax ∃!-syntax A (λ x → B) = ∃![ x ꞉ A ] B

open is-iso

Σ-pathP-iso
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
    {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  → Σ[ p ꞉ ＜ x .fst ／ A ＼ y .fst ＞ ] ＜ x .snd ／ (λ i → B i (p i)) ＼ y .snd ＞
  ≅ ＜ x ／ (λ i → Σ (A i) (B i)) ＼ y ＞
Σ-pathP-iso .fst (p , q) i = p i , q i
Σ-pathP-iso .snd .inv p = (λ i → p i .fst) , (λ i → p i .snd)
Σ-pathP-iso .snd .rinv x = refl
Σ-pathP-iso .snd .linv x = refl

Σ-path-iso
  : {x y : Σ A B}
  → Σ[ p ꞉ x .fst ＝ y .fst ] (subst B p (x .snd) ＝ y .snd)
  ≅ (x ＝ y)
Σ-path-iso {B} {x} {y} = transport
  (λ i → (Σ[ p ꞉ x .fst ＝ y .fst ] (pathP＝path (λ j → B (p j)) (x .snd) (y .snd) i))
       ≅ (x ＝ y))
  Σ-pathP-iso

×-path : {B : Type ℓ′} {a c : A} {b d : B}
       → a ＝ c → b ＝ d → (a , b) ＝ (c , d)
×-path ac bd i = (ac i , bd i)

Σ-ap-snd : Π[ x ꞉ A ] (P x ≃ Q x) → Σ A P ≃ Σ A Q
Σ-ap-snd {A} {P} {Q} pointwise = iso→equiv morp where
  pwise : Π[ x ꞉ A ] (P x ≅ Q x)
  pwise x = _ , is-equiv→is-iso (pointwise x .snd)

  morp : Σ _ P ≅ Σ _ Q
  morp .fst (i , x) = i , pointwise i .fst x
  morp .snd .inv (i , x) = i , pwise i .snd .inv x
  morp .snd .rinv (i , x) = ap² _,_ refl (pwise i .snd .rinv _)
  morp .snd .linv (i , x) = ap² _,_ refl (pwise i .snd .linv _)

Σ-ap-fst : (e : A ≃ A′) → Σ A (B ∘ e .fst) ≃ Σ A′ B
Σ-ap-fst {A} {A′} {B} e = intro , intro-is-equiv
 where
  intro : Σ _ (B ∘ e .fst) → Σ _ B
  intro (a , b) = e .fst a , b

  intro-is-equiv : is-equiv intro
  intro-is-equiv .equiv-proof x = ctr , is-ctr where
    PB : ∀ {x y} → x ＝ y → B x → B y → Type _
    PB p = PathP (λ i → B (p i))

    open Σ x renaming (fst to a′; snd to b)
    open Σ (e .snd .equiv-proof a′ .fst) renaming (fst to A-ctr; snd to α)

    B-ctr : B (e .fst A-ctr)
    B-ctr = subst B (sym α) b

    P-ctr : PB α B-ctr b
    P-ctr i = coe1→i (λ i → B (α i)) i b

    ctr : fibre intro x
    ctr = (A-ctr , B-ctr) , Σ-pathP α P-ctr

    is-ctr : ∀ y → ctr ＝ y
    is-ctr ((r , s) , p) = λ i → (a＝r i , b≠s i) , Σ-pathP (α＝ρ i) (coh i) where
      open Σ (Σ-pathP-iso .snd .inv p) renaming (fst to ρ; snd to σ)
      open Σ (Σ-pathP-iso .snd .inv (e .snd .equiv-proof a′ .snd (r , ρ)))
        renaming (fst to a＝r; snd to α＝ρ)

      b≠s : PB (ap (e .fst) a＝r) B-ctr s
      b≠s i = comp (λ k → B (α＝ρ i (~ k))) (∂ i) λ where
        k (i = i0) → P-ctr (~ k)
        k (i = i1) → σ (~ k)
        k (k = i0) → b

      coh : ＜ P-ctr ／ (λ i → PB (α＝ρ i) (b≠s i) b) ＼ σ ＞
      coh i j = fill (λ k → B (α＝ρ i (~ k))) (∂ i) (~ j) λ where
        k (i = i0) → P-ctr (~ k)
        k (i = i1) → σ (~ k)
        k (k = i0) → b

Σ-ap : (e : A ≃ A′)
     → Π[ a ꞉ A ] (P a ≃ Q (e .fst a))
     → Σ A P ≃ Σ A′ Q
Σ-ap e e′ = Σ-ap-snd e′ ∙ₑ Σ-ap-fst e

×-ap : {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴}
     → A ≃ C → B ≃ D → A × B ≃ C × D
×-ap ac bd = Σ-ap ac (λ _ → bd)

Σ-assoc : {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″}
        → Σ[ x ꞉ A ] Σ[ y ꞉ B x ] C x y
        ≃ Σ[ (x , y) ꞉ Σ _ B ] C x y
Σ-assoc .fst (x , y , z) = (x , y) , z
Σ-assoc .snd .equiv-proof y .fst = strict-contr-fibres (λ { ((x , y) , z) → x , y , z}) y .fst
Σ-assoc .snd .equiv-proof y .snd = strict-contr-fibres (λ { ((x , y) , z) → x , y , z}) y .snd

Σ-Π-distrib : {B : A → Type ℓ′} {C : (x : A) → B x → Type ℓ″}
            → Π[ x ꞉ A ] Σ[ y ꞉ B x ] C x y
            ≃ Σ[ f ꞉ Π[ x ꞉ A ] B x ] Π[ x ꞉ A ] C x (f x)
Σ-Π-distrib .fst f = (λ x → f x .fst) , λ x → f x .snd
Σ-Π-distrib .snd .equiv-proof y .fst = strict-contr-fibres (λ f x → f .fst x , f .snd x) y .fst
Σ-Π-distrib .snd .equiv-proof y .snd = strict-contr-fibres (λ f x → f .fst x , f .snd x) y .snd

Σ-prop-path : (∀ x → is-prop (B x))
            → {x y : Σ _ B}
            → (x .fst ＝ y .fst) → x ＝ y
Σ-prop-path bp {x} {y} p i = p i , is-prop→pathP (λ i → bp (p i)) (x .snd) (y .snd) i

Σ-prop-path-is-equiv
  : (bp : ∀ x → is-prop (B x))
  → {x y : Σ _ B}
  → is-equiv (Σ-prop-path bp {x} {y})
Σ-prop-path-is-equiv bp {x} {y} = is-iso→is-equiv isom where
  isom : is-iso _
  isom .inv = ap fst
  isom .linv p = refl
  isom .is-iso.rinv p i j
    = p j .fst
    , is-prop→pathP (λ k → path-is-of-hlevel 1 (bp (p k .fst))
                                      {x = Σ-prop-path bp {x} {y} (ap fst p) k .snd}
                                      {y = p k .snd})
                             refl refl j i

Σ-prop-path-≃ : (∀ x → is-prop (B x))
              → {x y : Σ _ B}
              → (x .fst ＝ y .fst) ≃ (x ＝ y)
Σ-prop-path-≃ bp = Σ-prop-path bp , Σ-prop-path-is-equiv bp

Σ-prop-square
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → {w x y z : Σ _ B}
  → (∀ x → is-prop (B x))
  → {p : x ＝ w} {q : x ＝ y} {r : y ＝ z} {s : w ＝ z}
  → Square (ap fst p) (ap fst q) (ap fst r) (ap fst s)
  → Square p q r s
Σ-prop-square B-prop sq i j .fst = sq i j
Σ-prop-square B-prop {p} {q} {r} {s} sq i j .snd =
  is-prop→squareP (λ i j → B-prop (sq i j)) (ap snd q) (ap snd p) (ap snd s) (ap snd r) i j

Σ-contract-fst : (A-c : is-contr A) → Σ[ x ꞉ A ] B x ≃ B (centre A-c)
Σ-contract-fst {B} A-c = iso→equiv the-iso where
  the-iso : Iso _ _
  the-iso .fst (x , b) = subst B (sym $ paths A-c x) b
  the-iso .snd .inv = _ ,_
  the-iso .snd .rinv b′
    = sym $ subst-filler B refl b′
    ∙ ap (λ f → subst B f b′) (is-prop-β (is-contr→is-prop (path-is-of-hlevel 0 A-c)) _ _)
  the-iso .snd .linv (x , b) = Σ-pathP (paths A-c _) $ symP $ subst-filler B (sym $ paths A-c _) b

Σ-contract-snd : (∀ x → is-contr (B x)) → Σ A B ≃ A
Σ-contract-snd B-contr = iso→equiv the-iso where
  the-iso : Iso _ _
  the-iso .fst (a , b) = a
  the-iso .snd .inv x = x , centre (B-contr _)
  the-iso .snd .rinv x = refl
  the-iso .snd .linv (a , b) i = a , paths (B-contr a) b i

Σ-map-snd : ({x : A} → P x → Q x) → Σ _ P → Σ _ Q
Σ-map-snd f (x , y) = (x , f y)

Σ-pathP-dep
  : {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ′}
  → {x : Σ _ (B i0)} {y : Σ _ (B i1)}
  → (p : ＜ x .fst ／ A ＼ y .fst ＞)
  → ＜ x .snd ／ (λ i → B i (p i)) ＼ y .snd ＞
  → ＜ x ／ (λ i → Σ (A i) (B i)) ＼ y ＞
Σ-pathP-dep p q i = p i , q i

_,ₚ_ = Σ-pathP-dep
infixr 4 _,ₚ_

Σ-prop-pathP
  : {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ′}
  → (∀ i x → is-prop (B i x))
  → {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  → ＜ x .fst ／ A ＼ y .fst ＞
  → ＜ x ／ (λ i → Σ (A i) (B i)) ＼ y ＞
Σ-prop-pathP bp {x} {y} p i =
  p i , is-prop→pathP (λ i → bp i (p i)) (x .snd) (y .snd) i

Σ-inj-set
  : ∀ {x y z}
  → is-set A
  → Path (Σ A B) (x , y) (x , z)
  → y ＝ z
Σ-inj-set {B} {y} {z} A-set path =
  subst (_＝ z) (ap (λ e → transport (ap B e) y) (is-set-β A-set _ _ _ _) ∙ transport-refl y)
    (from-pathP (ap snd path))

Σ-swap
  : {B : Type ℓ′} {C : A → B → Type ℓ″}
  → Σ[ x ꞉ A ] Σ[ y ꞉ B ] C x y
  ≃ Σ[ y ꞉ B ] Σ[ x ꞉ A ] C x y
Σ-swap .fst (x , y , f) = y , x , f
Σ-swap .snd .equiv-proof = strict-contr-fibres _

×-swap : {B : Type ℓ′} → A × B ≃ B × A
×-swap .fst (x , y) = y , x
×-swap .snd .equiv-proof = strict-contr-fibres _
