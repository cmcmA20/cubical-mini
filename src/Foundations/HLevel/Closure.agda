{-# OPTIONS --safe #-}
module Foundations.HLevel.Closure where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Path.Base
open import Foundations.Path.Groupoid
open import Foundations.Sigma.Properties
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A B C : Type ℓ

open Iso

retract→is-contr : Retractₜ B A → is-contr A → is-contr B
retract→is-contr (f , s) c .fst = f (centre c)
retract→is-contr (f , s) c .snd x =
  f (centre c)      ~⟨ ap f (paths c _) ⟩
  f (s .section x)  ~⟨ s .is-section # x ⟩
  x                 ∎

opaque
  retract→is-prop : Retractₜ B A → is-prop A → is-prop B
  retract→is-prop (f , s) propA x y =
    x                 ~⟨ s .is-section # x ⟨
    f (s .section x)  ~⟨ ap f (propA _ _) ⟩
    f (s .section y)  ~⟨ s .is-section # y ⟩
    y                 ∎

retract→is-of-hlevel : (n : HLevel)
                     → Retractₜ B A
                     → is-of-hlevel n A
                     → is-of-hlevel n B
retract→is-of-hlevel 0 = retract→is-contr
retract→is-of-hlevel 1 = retract→is-prop
retract→is-of-hlevel (suc (suc h)) (f , hs) hlevel x y =
  retract→is-of-hlevel (suc h) (sect , make-section (ap g) inv) (hlevel (g x) (g y))
  where
    g = hs .section
    p = hs .is-section

    sect : g x ＝ g y → x ＝ y
    sect path =
      x        ~⟨ p # x ⟨
      f (g x)  ~⟨ ap f path ⟩
      f (g y)  ~⟨ p # y ⟩
      y        ∎

    inv : sect retraction-of (ap g)
    inv = fun-ext λ path →
      p # x ⁻¹ ∙ ap (g ∙ f) path ∙ p # y ∙ refl  ~⟨ p # x ⁻¹ ◁ ap (g ∙ f) path ◁ ∙-id-i (p # y) ⟩
      p # x ⁻¹ ∙ ap (g ∙ f) path ∙ p # y         ~⟨ p # x ⁻¹ ◁ homotopy-natural (p #_) path ⁻¹ ⟩
      p # x ⁻¹ ∙ p # x ∙ path                    ~⟨ ∙-assoc _ _ _ ⟩
      (p # x ⁻¹ ∙ p # x) ∙ path                  ~⟨ ∙-inv-o (p # x) ▷ path ⟩
      refl ∙ path                                ~⟨ ∙-id-o path ⟩
      path                                       ∎

qinv→is-of-hlevel : (h : HLevel) (f : A → B) → quasi-inverse f → is-of-hlevel h A → is-of-hlevel h B
qinv→is-of-hlevel h f fi = retract→is-of-hlevel h (qinv→retract⁻ f fi)

is-equiv→is-of-hlevel : (h : HLevel) (f : A → B) → is-equiv f → is-of-hlevel h A → is-of-hlevel h B
is-equiv→is-of-hlevel h f eqv = qinv→is-of-hlevel h f (is-equiv→qinv eqv)

≅→is-of-hlevel : (h : HLevel) → B ≅ A → is-of-hlevel h A → is-of-hlevel h B
≅→is-of-hlevel h i = retract→is-of-hlevel h (i .from , ≅→from-has-section i)

≃→is-of-hlevel : (h : HLevel) → (B ≃ A) → is-of-hlevel h A → is-of-hlevel h B
≃→is-of-hlevel h e = ≅→is-of-hlevel h (≃→≅ e)

Π-is-of-hlevel : {A : Type ℓ} {B : A → Type ℓ′} (h : HLevel)
                 (Bhl : Π[ x ꞉ A ] is-of-hlevel h (B x))
               → is-of-hlevel h (Π[ x ꞉ A ] B x)
Π-is-of-hlevel 0 bhl = (λ _ → bhl _ .fst) , λ x i a → bhl _ .snd (x a) i
Π-is-of-hlevel 1 bhl f g i a = bhl a (f a) (g a) i
Π-is-of-hlevel (suc (suc h)) bhl f g = retract→is-of-hlevel (suc h) (fun-ext , make-section happly (λ _ → refl))
  (Π-is-of-hlevel (suc h) λ x → bhl x (f x) (g x))

∀-is-of-hlevel : {B : A → Type ℓ′} (h : HLevel)
                 (Bhl : (x : A) → is-of-hlevel h (B x))
               → is-of-hlevel h ({x : A} → B x)
∀-is-of-hlevel h bhl = retract→is-of-hlevel h (implicit , make-section (λ f _ → f) λ _ → refl)
  (Π-is-of-hlevel h bhl)

Π²-is-of-hlevel
  : {B : A → Type ℓ′} {C : ∀ a → B a → Type ℓ″}
  → (n : HLevel) (Bhl : (x : A) (y : B x) → is-of-hlevel n (C x y))
  → is-of-hlevel n (∀ x y → C x y)
Π²-is-of-hlevel n w = Π-is-of-hlevel n λ _ → Π-is-of-hlevel n (w _)

Π³-is-of-hlevel
  : {B : A → Type ℓ′} {C : ∀ a → B a → Type ℓ″} {D : ∀ a b → C a b → Type ℓ‴}
  → (n : HLevel) (Bhl : (x : A) (y : B x) (z : C x y) → is-of-hlevel n (D x y z))
  → is-of-hlevel n (∀ x y z → D x y z)
Π³-is-of-hlevel n w = Π-is-of-hlevel n λ _ → Π²-is-of-hlevel n (w _)

fun-is-of-hlevel
  : {B : Type ℓ′}
  → (n : HLevel) → is-of-hlevel n B
  → is-of-hlevel n (A → B)
fun-is-of-hlevel n hl = Π-is-of-hlevel n (λ _ → hl)

Σ-is-of-hlevel : {A : Type ℓ} {B : A → Type ℓ′} (n : HLevel)
               → is-of-hlevel n A
               → ((x : A) → is-of-hlevel n (B x))
               → is-of-hlevel n (Σ A B)
Σ-is-of-hlevel 0 acontr bcontr =
  (acontr .fst , bcontr _ .fst) ,
    λ x →  acontr .snd _
        ,ₚ is-prop→pathᴾ (λ _ → is-contr→is-prop (bcontr _)) _ _
Σ-is-of-hlevel 1 aprop bprop (a , b) (a' , b') i =
  (aprop a a' i) , (is-prop→pathᴾ (λ i → bprop (aprop a a' i)) b b' i)
Σ-is-of-hlevel {B} (suc (suc n)) h1 h2
  = pathᴾ-is-of-hlevel (suc n) λ w z
  → ≅→is-of-hlevel (suc n) (Σ-pathᴾ-iso ⁻¹)
  $ Σ-is-of-hlevel (suc n) (h1 (w .fst) (z .fst)) λ p → pathᴾ-is-of-hlevel (suc n) (h2 _) (w .snd) (z .snd)

×-is-of-hlevel : {B : Type ℓ′}
               → (n : HLevel)
               → is-of-hlevel n A → is-of-hlevel n B
               → is-of-hlevel n (A × B)
×-is-of-hlevel n ahl bhl = Σ-is-of-hlevel n ahl (λ _ → bhl)

Lift-is-of-hlevel : (n : HLevel)
                  → is-of-hlevel n A
                  → is-of-hlevel n (Lift ℓ′ A)
Lift-is-of-hlevel n a-hl = retract→is-of-hlevel n (lift , make-section lower (λ _ → refl)) a-hl

≃-is-of-hlevel : (n : HLevel) → is-of-hlevel n A → is-of-hlevel n B → is-of-hlevel n (A ≃ B)
≃-is-of-hlevel {A} {B} zero Ahl Bhl = e , deform where
  e : A ≃ B
  e = (λ _ → Bhl .fst) , is-contr→is-equiv Ahl Bhl

  deform : (e′ : A ≃ B) → e ＝ e′
  deform (g , _) = Σ-path (λ i x → Bhl .snd (g x) i)
                          (is-equiv-is-prop _ _ _)

≃-is-of-hlevel (suc n) _ Bhl =
  Σ-is-of-hlevel (suc n)
    (fun-is-of-hlevel (suc n) Bhl)
    λ f → is-prop→is-of-hlevel-suc {h = n} (is-equiv-is-prop f)

opaque
  ≃-is-of-hlevel-left-suc : (n : HLevel) → is-of-hlevel (suc n) A → is-of-hlevel (suc n) (A ≃ B)
  ≃-is-of-hlevel-left-suc zero    A-hl e =
    ≃-is-of-hlevel 1 A-hl (retract→is-prop (e .fst , make-section (e ⁻¹ $_) (Equiv.ε e)) A-hl) e
  ≃-is-of-hlevel-left-suc (suc n) A-hl e =
    ≃-is-of-hlevel (suc (suc n)) A-hl (≃→is-of-hlevel (suc (suc n)) (e ⁻¹) A-hl) e

  ≃-is-of-hlevel-right-suc : (n : HLevel) → is-of-hlevel (suc n) B → is-of-hlevel (suc n) (A ≃ B)
  ≃-is-of-hlevel-right-suc zero    B-hl e =
    ≃-is-of-hlevel 1 (retract→is-prop ((e ⁻¹ $_) , make-section (e .fst) (Equiv.η e ⁻¹)) B-hl) B-hl e
  ≃-is-of-hlevel-right-suc (suc n) B-hl e =
    ≃-is-of-hlevel (suc (suc n)) (≃→is-of-hlevel (suc (suc n)) e B-hl) B-hl e

@0 =-is-of-hlevel : (n : ℕ) → is-of-hlevel n A → is-of-hlevel n B → is-of-hlevel n (A ＝ B)
=-is-of-hlevel n Ahl Bhl = is-equiv→is-of-hlevel n ua univalence⁻¹ (≃-is-of-hlevel n Ahl Bhl)


instance opaque
  H-Level-Π : ∀ {h} {A : Type ℓ} {B : A → Type ℓ′}
            → ⦃ {a : A} → H-Level h (B a) ⦄
            → H-Level h (Π[ a ꞉ A ] B a)
  H-Level-Π {h} .H-Level.has-of-hlevel = Π-is-of-hlevel h λ _ → hlevel h
  {-# OVERLAPPABLE H-Level-Π #-}

  H-Level-∀ : ∀ {h} {A : Type ℓ} {B : A → Type ℓ′}
            → ⦃ {a : A} → H-Level h (B a) ⦄
            → H-Level h (∀[ a ꞉ A ] B a)
  H-Level-∀ {h} .H-Level.has-of-hlevel = ∀-is-of-hlevel h λ _ → hlevel h
  {-# OVERLAPPABLE H-Level-∀ #-}

  H-Level-Σ : ∀ {h} {A : Type ℓ} {B : A → Type ℓ′}
            → ⦃ H-Level h A ⦄
            → ⦃ {a : A} → H-Level h (B a) ⦄
            → H-Level h (Σ[ a ꞉ A ] B a)
  H-Level-Σ {h} .H-Level.has-of-hlevel = Σ-is-of-hlevel h (hlevel h) λ _ → hlevel h
  {-# OVERLAPPABLE H-Level-Σ #-}

  -- H-Level-Pathᴾ-same : ∀ {h} {P : I → Type ℓ}
  --                    → ⦃ H-Level h (P i1) ⦄
  --                    → ∀ {x y}
  --                    → H-Level h ＜ x ／ P ＼ y ＞
  -- H-Level-Pathᴾ-same .H-Level.has-of-hlevel = pathᴾ-is-of-hlevel-same _ (hlevel _)
  -- {-# INCOHERENT H-Level-Pathᴾ-same #-}

  H-Level-Pathᴾ : ∀ {h} {P : I → Type ℓ}
                → ⦃ H-Level (suc h) (P i1) ⦄
                → ∀ {x y}
                → H-Level h ＜ x ／ P ＼ y ＞
  H-Level-Pathᴾ {h} .H-Level.has-of-hlevel = pathᴾ-is-of-hlevel h (hlevel (suc h)) _ _
  {-# OVERLAPPABLE H-Level-Pathᴾ #-}

  H-Level-Lift : ∀ {h} ⦃ hl : H-Level h A ⦄ → H-Level h (Lift ℓ′ A)
  H-Level-Lift {h} .H-Level.has-of-hlevel = Lift-is-of-hlevel h (hlevel h)

  H-Level-≃-l : ∀ {h} ⦃ hl : H-Level (suc h) A ⦄ → H-Level (suc h) (A ≃ B)
  H-Level-≃-l {h} .H-Level.has-of-hlevel = ≃-is-of-hlevel-left-suc h (hlevel (suc h))
  {-# INCOHERENT H-Level-≃-l #-}

  H-Level-≃-r : ∀ {h} ⦃ hl : H-Level (suc h) B ⦄ → H-Level (suc h) (A ≃ B)
  H-Level-≃-r {h} .H-Level.has-of-hlevel = ≃-is-of-hlevel-right-suc h (hlevel (suc h))
  {-# OVERLAPPING H-Level-≃-r #-}

  H-Level-≃ : ∀ {h} → ⦃ A-hl : H-Level h A ⦄ → ⦃ B-hl : H-Level h B ⦄ → H-Level h (A ≃ B)
  H-Level-≃ {h} .H-Level.has-of-hlevel = ≃-is-of-hlevel h (hlevel h) (hlevel h)
  {-# INCOHERENT H-Level-≃ #-}

  @0 H-Level-univalence
    : ∀ {h} {A B : Type ℓ} → ⦃ A-hl : H-Level h A ⦄ → ⦃ B-hl : H-Level h B ⦄ → H-Level h (A ＝ B)
  H-Level-univalence .H-Level.has-of-hlevel = =-is-of-hlevel _ (hlevel _) (hlevel _)
  {-# INCOHERENT H-Level-univalence #-}



-- Automation

≃→is-of-hlevel! : (h : HLevel) → B ≃ A → ⦃ A-hl : H-Level h A ⦄ → is-of-hlevel h B
≃→is-of-hlevel! h e = ≃→is-of-hlevel h e (hlevel h)

≅→is-of-hlevel! : (h : HLevel) → B ≅ A → ⦃ A-hl : H-Level h A ⦄ → is-of-hlevel h B
≅→is-of-hlevel! h e = ≅→is-of-hlevel h e (hlevel h)


-- by Martin Escardo
-- using retracts is crucial, because isomorphism proof is incredibly painful
module _ {f : A → B} (fi : quasi-inverse f) where private
  open import Foundations.Transport
  open quasi-inverse fi renaming ( inv   to g
                                 ; inv-i to v
                                 ; inv-o to u
                                 )

  qinv→is-equiv′ : is-equiv f
  qinv→is-equiv′ .equiv-proof y .fst .fst = g y
  qinv→is-equiv′ .equiv-proof y .fst .snd = u # y
  qinv→is-equiv′ .equiv-proof y .snd = retract→is-prop go
    (is-contr→is-prop (singletonₚ-is-contr (y , refl))) (g y , u # y)
    where
    go =
      Σ[ x  ꞉ A ] (f x ＝ y)         ~⟨ ≅→retract (≃→≅ (Σ-ap-snd (λ _ → sym-≃))) ⟩
      Σ[ x  ꞉ A ] (y   ＝ f x)       ~⟨ Σ-retract-fst (g , make-section f v) ⟩
      Σ[ y′ ꞉ B ] (y   ＝ f (g y′))  ~⟨ ≅→retract (≃→≅ (Σ-ap-snd λ y′ → subst-≃ (y ＝_) (u # y′ ⁻¹)))  ⟩
      Σ[ y′ ꞉ B ] (y   ＝ y′)        ∎
