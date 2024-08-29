{-# OPTIONS --safe #-}
module Foundations.Erased where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Univalence
open import Foundations.HLevel
open import Foundations.Pi
open import Foundations.Sigma

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  @0 A : Type ℓᵃ
  @0 B : Type ℓᵇ
  @0 C : Type ℓᶜ

record Recomputable {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field recompute : Erased A → A

open Recomputable public

@0 fibreᴱ≃fibre : {@0 f : A → B} {@0 y : B} → fibreᴱ f y ≃ fibre f y
fibreᴱ≃fibre = Σ-ap-snd λ _ → erased≃id

is-contr→is-contrᴱ : is-contr A → is-contrᴱ A
is-contr→is-contrᴱ (c , p) = (c , erase p)

opaque
  @0 is-of-hlevelᴱ≃is-of-hlevel : {n : HLevel} → is-of-hlevelᴱ n A ≃ is-of-hlevel n A
  is-of-hlevelᴱ≃is-of-hlevel {n = 0} = Σ-ap-snd λ _ → erased≃id
  is-of-hlevelᴱ≃is-of-hlevel {n = 1} = ≅→≃ $ to , iso from (λ _ → refl) li where
    to : is-propᴱ A → is-prop A
    to pr x y = pr x y .fst
    from : is-prop A → is-propᴱ A
    from pr x y = pr _ _ , erase (is-prop→is-set pr _ _ _)
    li : (pr : is-propᴱ A) → from (to pr) ＝ pr
    li {A} pr = fun-ext λ _ → fun-ext λ _ → Σ-prop-path go refl where
      go : {x y : A} (p : x ＝ y) → is-prop (Erased (is-central p))
      go {x} {y} p (erase u) (erase v) = let _ , erase w  = pr x y
        in congᴱ $ erase (fun-ext (λ _ → is-of-hlevel-+ 1 2 (to pr) _ _ _ _ _ _))
  is-of-hlevelᴱ≃is-of-hlevel {n = suc (suc n)} = Π-cod-≃ λ _ → Π-cod-≃ λ _ → is-of-hlevelᴱ≃is-of-hlevel

@0 is-equivᴱ≃is-equiv : {f : A → B} → is-equivᴱ f ≃ is-equiv f
is-equivᴱ≃is-equiv {B} {f} =
  Π-cod-≃ (λ _ → is-of-hlevelᴱ≃is-of-hlevel ∙ generic-ae is-contr fibreᴱ≃fibre ) ∙ ≅→≃ go where
    go : Π[ b ꞉ B ] (is-contr (fibre f b)) ≅ is-equiv f
    go .fst h .equiv-proof = h
    go .snd .is-iso.inv eqv = eqv .equiv-proof
    go .snd .is-iso.rinv eqv i .equiv-proof = eqv .equiv-proof
    go .snd .is-iso.linv _ = refl


@0 equivᴱ≃equiv : (A ≃ᴱ B) ≃ (A ≃ B)
equivᴱ≃equiv = Σ-ap-snd λ _ → is-equivᴱ≃is-equiv

@0 is-isoᴱ≃is-iso : {@0 f : A → B} → is-isoᴱ f ≃ is-iso f
is-isoᴱ≃is-iso = Σ-ap-snd (λ _ → ×-ap erased≃id erased≃id) ∙ ≅→≃ λ where
  .fst → iso $³_
  .snd .is-iso.inv isi → is-iso.inv isi , is-iso.rinv isi , is-iso.linv isi
  .snd .is-iso.rinv isi _ .is-iso.inv x → isi .is-iso.inv x
  .snd .is-iso.rinv isi _ .is-iso.rinv x → isi .is-iso.rinv x
  .snd .is-iso.rinv isi _ .is-iso.linv x → isi .is-iso.linv x
  .snd .is-iso.linv x _ → x

is-isoᴱ→is-equivᴱ : {@0 f : A → B} → is-isoᴱ f → is-equivᴱ f
is-isoᴱ→is-equivᴱ {f} (inv , erase ri , erase li) y = (inv y , erase (eqv y .fst .snd)) , erase go where
  @0 eqv : _
  eqv = is-iso→is-equiv (iso inv ri li) .equiv-proof
  @0 go : is-central (inv y , erase (eqv y .fst .snd))
  go (c , erase p) i =
    let r = is-iso→fibre-is-prop (iso inv ri li) y (inv y) c (ri y) p
    in r i .fst , erase (r i .snd)

erased-path : {@0 A : Type ℓᵃ} {@0 x y : A} → Erased (x ＝ y) ≃ (erase x ＝ erase y)
erased-path .fst = congᴱ
erased-path .snd .equiv-proof = strict-contr-fibres uncongᴱ

module erased-path {ℓ} {@0 A} {@0 x} {@0 y} = Equiv (erased-path {ℓ} {A} {x} {y})

erased-is-of-hlevel : {@0 A : Type ℓᵃ} → (n : HLevel) → @0 is-of-hlevel n A → is-of-hlevel n (Erased A)
erased-is-of-hlevel 0 = erased-is-contr
erased-is-of-hlevel 1 = erased-is-prop
erased-is-of-hlevel (suc (suc n)) hl (erase x) (erase y) = ≃→is-of-hlevel (suc n)
  erased-path.inverse (erased-is-of-hlevel (suc n) (hl x y))

-- awful notation
infixr 30 _∙ᴱₑ_
_∙ᴱₑ_ : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ} → A ≃ᴱ B → B ≃ᴱ C → A ≃ᴱ C
(f , fe) ∙ᴱₑ (g , ge) = g ∘ f , e where
  fi = is-equivᴱ→is-isoᴱ fe
  f⁻¹ = fi .fst

  gi = is-equivᴱ→is-isoᴱ ge
  g⁻¹ = gi .fst

  opaque
    @0 right : (f⁻¹ ∘ g⁻¹) is-right-inverse-of (g ∘ f)
    right _ = ap g (fi .snd .fst .erased _) ∙ gi .snd .fst .erased _

    @0 left : (f⁻¹ ∘ g⁻¹) is-left-inverse-of (g ∘ f)
    left _ = ap f⁻¹ (gi .snd .snd .erased _) ∙ fi .snd .snd .erased _

  e : is-equivᴱ (g ∘ f)
  e = is-isoᴱ→is-equivᴱ $ (f⁻¹ ∘ g⁻¹) , erase right , erase left


fibre→fibreᴱ : {A : Type ℓᵃ} {B : Type ℓᵇ} {f : A → B} {y : B} → fibre f y → fibreᴱ f y
fibre→fibreᴱ = second (λ x → erase x)

is-equiv→is-equivᴱ : {A : Type ℓᵃ} {B : Type ℓᵇ} {f : A → B} → is-equiv f → is-equivᴱ f
is-equiv→is-equivᴱ fe y .fst = fibre→fibreᴱ $ fe .equiv-proof y .fst
is-equiv→is-equivᴱ fe y .snd .erased (c , erase p) i
  = fe .equiv-proof y .snd (c , p) i .fst
  , erase (fe .equiv-proof y .snd (c , p) i .snd)

≃→≃ᴱ : {A : Type ℓᵃ} {B : Type ℓᵇ} → A ≃ B → A ≃ᴱ B
≃→≃ᴱ = second is-equiv→is-equivᴱ

instance
  Symm-Erased-≃ : Symm (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) _≃ᴱ_
  Symm-Erased-≃ .sym e = is-equivᴱ→inverse (e .snd) , is-isoᴱ→is-equivᴱ
    ( e .fst
    , erase (λ x → is-equivᴱ→unit (e .snd) x .erased)
    , erase λ x → is-equivᴱ→counit (e .snd) x .erased )

  Trans-Erased-≃ : Trans (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) (_≃ᴱ_ {ℓ′ = ℓᶜ}) _≃ᴱ_
  Trans-Erased-≃ ._∙_  = _∙ᴱₑ_

Σ-contract-sndᴱ
  : {A : Type ℓᵃ} {B : A → Type ℓᵇ}
  → (∀ x → is-contrᴱ (B x)) → Σ A B ≃ᴱ A
Σ-contract-sndᴱ B-contr = fst , is-isoᴱ→is-equivᴱ
  ( (λ x → x , B-contr x .fst)
  , erase (λ _ → refl)
  , erase λ (a , b) i → a , B-contr a .snd .erased b i )

opaque
  unfolding ua
  equiv-is-contrᴱ : (A : Type ℓᵃ) → is-contrᴱ (Σ[ B ꞉ Type ℓᵃ ] (A ≃ B))
  equiv-is-contrᴱ A .fst = A , refl
  equiv-is-contrᴱ A .snd .erased (B , A≃B) i = ua A≃B i , p i , q i where
    p : ＜ id ／ (λ i → A → ua A≃B i) ＼ A≃B .fst ＞
    p i x = outS (ua-glue A≃B i (λ { (i = i0) → x }) (inS (A≃B .fst x)))

    q : ＜ id-is-equiv ／ (λ i → is-equiv (p i)) ＼ A≃B .snd ＞
    q = is-prop→pathᴾ (λ i → is-equiv-is-prop (p i)) _ _

instance
  H-Level-Erased : ∀ {h} → ⦃ @0 A-hl : H-Level h A ⦄
                 → H-Level h (Erased A)
  H-Level-Erased {h} .H-Level.has-of-hlevel = erased-is-of-hlevel h (hlevel h)
  {-# OVERLAPPING H-Level-Erased #-}
