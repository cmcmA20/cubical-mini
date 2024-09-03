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

open Iso

record Recomputable {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field recompute : Erased A → A

open Recomputable public

@0 fibreᴱ≃fibre : {@0 f : A → B} {@0 y : B} → fibreᴱ f y ≃ fibre f y
fibreᴱ≃fibre = Σ-ap-snd λ _ → erased≃id

is-contr→is-contrᴱ : is-contr A → is-contrᴱ A
is-contr→is-contrᴱ (c , p) = (c , erase p)

@0 is-of-hlevelᴱ≃is-of-hlevel : {n : HLevel} → is-of-hlevelᴱ n A ≃ is-of-hlevel n A
is-of-hlevelᴱ≃is-of-hlevel {n = 0} = Σ-ap-snd λ _ → erased≃id
is-of-hlevelᴱ≃is-of-hlevel {n = 1} = ≅→≃ $ iso
  (λ pr x y → pr x y .fst)
  (λ pr x y → pr _ _ , erase (is-prop→is-set pr _ _ _))
  refl
  (fun-ext λ pr → fun-ext λ x → fun-ext λ y → Σ-prop-path (go pr) refl)
  where
  go : (pr : (a b : A) → is-contrᴱ (a ＝ b)) {x y : A} (p : x ＝ y) → is-prop (Erased (is-central p))
  go pr {x} {y} p (erase u) (erase v) = let _ , erase w  = pr x y
    in congᴱ $ erase (fun-ext (λ _ → is-of-hlevel-+ 1 2 (λ w z → pr w z .fst) _ _ _ _ _ _))
is-of-hlevelᴱ≃is-of-hlevel {n = suc (suc n)} = Π-cod-≃ λ _ → Π-cod-≃ λ _ → is-of-hlevelᴱ≃is-of-hlevel

@0 is-equivᴱ≃is-equiv : {f : A → B} → is-equivᴱ f ≃ is-equiv f
is-equivᴱ≃is-equiv {B} {f} =
  Π-cod-≃ (λ _ → is-of-hlevelᴱ≃is-of-hlevel ∙ generic-ae is-contr fibreᴱ≃fibre ) ∙ ≅→≃ go where
    go : Π[ b ꞉ B ] (is-contr (fibre f b)) ≅ is-equiv f
    go .to h .equiv-proof = h
    go .from = equiv-proof
    go .inverses .Inverses.inv-o i x .equiv-proof = x .equiv-proof
    go .inverses .Inverses.inv-i = refl


@0 equivᴱ≃equiv : (A ≃ᴱ B) ≃ (A ≃ B)
equivᴱ≃equiv = Σ-ap-snd λ _ → is-equivᴱ≃is-equiv

@0 is-invᴱ≃is-inv : {@0 f : A → B} → is-invertibleᴱ f ≃ is-invertible f
is-invᴱ≃is-inv {f} = Σ-ap-snd (λ _ → ×-ap erased≃id erased≃id) ∙ ≅→≃ go where
  go : _ ≅ is-invertible f
  go .to = invertible $³_
  go .from x
    = x .is-invertible.inv
    , x .is-invertible.inverses .Inverses.inv-o
    , x .is-invertible.inverses .Inverses.inv-i
  go .inverses .Inverses.inv-o i x .is-invertible.inv = x .is-invertible.inv
  go .inverses .Inverses.inv-o i x .is-invertible.inverses .Inverses.inv-o =
    x .is-invertible.inverses .Inverses.inv-o
  go .inverses .Inverses.inv-o i x .is-invertible.inverses .Inverses.inv-i =
    x .is-invertible.inverses .Inverses.inv-i
  go .inverses .Inverses.inv-i = refl

is-invᴱ→is-equivᴱ : {@0 f : A → B} → is-invertibleᴱ f → is-equivᴱ f
is-invᴱ→is-equivᴱ {f} (inv , erase ri , erase li) y = (inv y , erase (eqv y .fst .snd)) , erase go where
  @0 eqv : _
  eqv = is-inv→is-equiv (invertible inv ri li) .equiv-proof
  @ 0 go : is-central (inv y , erase (eqv y .fst .snd))
  go (c , erase p) i =
    let r = is-inv→fibre-is-prop (invertible inv ri li) y (inv y) c (ri # y) p
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
(f , fe) ∙ᴱₑ (g , ge) = f ∙ g , e where
  open is-invertible
  fi = is-equivᴱ→is-invᴱ fe
  gi = is-equivᴱ→is-invᴱ ge

  f⁻¹ = fi .fst
  g⁻¹ = gi .fst

  opaque
    @0 s : (g⁻¹ ∙ f⁻¹) section-of (f ∙ g)
    s = apᶠ g⁻¹ (fi .snd .fst .erased) g ∙ gi .snd .fst .erased

    @0 r : (g⁻¹ ∙ f⁻¹) retract-of (f ∙ g)
    r = apᶠ f (gi .snd .snd .erased) f⁻¹ ∙ fi .snd .snd .erased

  e : is-equivᴱ (f ∙ g)
  e = is-invᴱ→is-equivᴱ $ (g⁻¹ ∙ f⁻¹) , erase s , erase r

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
  Sym-Erased-≃ : Sym (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) _≃ᴱ_
  Sym-Erased-≃ .sym e = is-equivᴱ→inverse (e .snd) , is-invᴱ→is-equivᴱ
    (e .fst
    , erase (fun-ext λ x → is-equivᴱ→unit (e .snd) x .erased)
    , erase (fun-ext λ x → is-equivᴱ→counit (e .snd) x .erased) )

  Trans-Erased-≃ : Trans (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) (_≃ᴱ_ {ℓ′ = ℓᶜ}) _≃ᴱ_
  Trans-Erased-≃ ._∙_  = _∙ᴱₑ_

Σ-contract-sndᴱ
  : {A : Type ℓᵃ} {B : A → Type ℓᵇ}
  → (∀ x → is-contrᴱ (B x)) → Σ A B ≃ᴱ A
Σ-contract-sndᴱ B-contr = fst , is-invᴱ→is-equivᴱ
  ( (λ x → x , B-contr x .fst)
  , erase refl
  , erase λ i (a , b) → a , B-contr a .snd .erased b i )

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
