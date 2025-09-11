{-# OPTIONS --safe #-}
module Data.AF.Prop.Ramsey where

open import Meta.Prelude
open import Meta.Effect
open Variadics _

open import Data.AF.Prop
open import Data.Sum.Base
open import Data.Truncation.Propositional as ∥-∥₁

-- double induction

af₁-double-ind : ∀ {ℓ ℓ′ ℓ″} {A : 𝒰 ℓ} {P : (A → A → 𝒰 ℓ′) → (A → A → 𝒰 ℓ′) → 𝒰 ℓ″}
               → ((R T : A → A → 𝒰 ℓ′) → is-prop (P R T))
               → ((R T : A → A → 𝒰 ℓ′) → (∀ x y → ∥ R x y ∥₁) → AF₁ T → P R T)
               → ((R T : A → A → 𝒰 ℓ′) → AF₁ R → (∀ x y → ∥ T x y ∥₁) → P R T)
               → ((R T : A → A → 𝒰 ℓ′) → (∀ x → P (R ↑₁ x) T) → (∀ x → P R (T ↑₁ x)) → P R T)
               → {R T : A → A → 𝒰 ℓ′} → AF₁ R → AF₁ T → P R T
af₁-double-ind Pp Hl Hr H2    (AF₁full afr)         at                       = Hl _ _ afr at
af₁-double-ind Pp Hl Hr H2 ar@(AF₁lift alr)            (AF₁full aft)         = Hr _ _ ar aft
af₁-double-ind Pp Hl Hr H2 ar@(AF₁lift alr)         at@(AF₁lift alt)         =
  H2 _ _
    (λ x → af₁-double-ind Pp Hl Hr H2 (alr x) at)
    (λ x → af₁-double-ind Pp Hl Hr H2 ar (alt x))
af₁-double-ind Pp Hl Hr H2 ar@(AF₁lift alr)            (AF₁squash at₁ at₂ i) =
  Pp _ _ (af₁-double-ind Pp Hl Hr H2 ar at₁) (af₁-double-ind Pp Hl Hr H2 ar at₂) i
af₁-double-ind Pp Hl Hr H2    (AF₁squash ar₁ ar₂ i) at                       =
  Pp _ _ (af₁-double-ind Pp Hl Hr H2 ar₁ at) (af₁-double-ind Pp Hl Hr H2 ar₂ at) i

af₁-zero-inter-rec : ∀ {ℓ ℓ′ ℓ″} {X : 𝒰 ℓ} {A B : 𝒰 ℓ′} {R T : X → X → 𝒰 ℓ″}
                  → AF₁ R → AF₁ T
                  → (C : X → X → 𝒰 ℓ′)
                  → (∀ x y → ∥ R x y ∥₁ → C x y ⊎₁ A)
                  → (∀ x y → ∥ T x y ∥₁ → C x y ⊎₁ B)
                  → AF₁ (λ x y → C x y ⊎₁ A × B)
af₁-zero-inter-rec {ℓ′} {X} {A} {B} =
  af₁-double-ind
    {P = λ U V → (C : X → X → 𝒰 ℓ′)
               → (∀ x y → ∥ U x y ∥₁ → C x y ⊎₁ A)
               → (∀ x y → ∥ V x y ∥₁ → C x y ⊎₁ B)
               → AF₁ (λ x y → C x y ⊎₁ A × B)}
    (λ _ _ → hlevel 1)
    (λ U V Uf Va C ui vi →
      af₁-mono
        (λ {x} {y} vxy →
           rec! [ ∣_∣₁ ∘ inl
                , (λ b → map (map-r (_, b))
                             (ui x y (Uf x y)))
                ]ᵤ
             (vi x y ∣ vxy ∣₁))
        Va)
    (λ U V Ua Vf C ui vi →
      af₁-mono
        (λ {x} {y} uxy →
           rec! [ ∣_∣₁ ∘ inl
                , (λ a → map (map-r (a ,_))
                             (vi x y (Vf x y)))
                ]ᵤ
             (ui x y ∣ uxy ∣₁))
        Ua)
    λ U V Ul Vl C ui vi →
      AF₁lift λ a →
      af₁-mono
         -- TODO prettify
         (λ {x} {y} → rec! [ rec! [ ∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl
                                  , ∣_∣₁ ∘ inr ∘ ∣_∣₁ ∘ inl ]ᵤ
                           , ∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inr ]ᵤ)
         (Ul a (C ↑₁ a)
                 (λ x y → rec! [ map (map-l (∣_∣₁ ∘ inl)) ∘ ui x y ∘ ∣_∣₁
                               , map (map-l (∣_∣₁ ∘ inr)) ∘ ui a x ∘ ∣_∣₁ ]ᵤ)
                 (λ x y → map (map-l (∣_∣₁ ∘ inl)) ∘ vi x y))

af₁-zero-inter : ∀ {ℓ ℓ′} {X : 𝒰 ℓ} {A B : 𝒰 ℓ′} {R : X → X → 𝒰 ℓ′}
              → AF₁ (λ x y → R x y ⊎₁ A)
              → AF₁ (λ x y → R x y ⊎₁ B)
              → AF₁ (λ x y → R x y ⊎₁ A × B)
af₁-zero-inter {R} afa afb = af₁-zero-inter-rec afa afb R (λ x y → proj!) (λ x y → proj!)

af₁-one-inter-rec : ∀ {ℓ ℓ′ ℓ″} {X : 𝒰 ℓ} {A B : X → 𝒰 ℓ′} {R T : X → X → 𝒰 ℓ″}
                  → AF₁ R → AF₁ T
                  → (C : X → X → 𝒰 ℓ′)
                  → (∀ x y → ∥ R x y ∥₁ → C x y ⊎₁ A x)
                  → (∀ x y → ∥ T x y ∥₁ → C x y ⊎₁ B x)
                  → AF₁ (λ x y → C x y ⊎₁ A x × B x)
af₁-one-inter-rec {ℓ′} {X} {A} {B} =
  af₁-double-ind
    {P = λ U V → (C : X → X → 𝒰 ℓ′)
               → (∀ x y → ∥ U x y ∥₁ → C x y ⊎₁ A x)
               → (∀ x y → ∥ V x y ∥₁ → C x y ⊎₁ B x)
               → AF₁ (λ x y → C x y ⊎₁ A x × B x)}
    (λ _ _ → hlevel 1)
    (λ U V Uf Va C ui vi →
       af₁-mono
        (λ {x} {y} vxy →
           rec! [ ∣_∣₁ ∘ inl
                , (λ bx → map (map-r (_, bx))
                             (ui x y (Uf x y)))
                ]ᵤ
             (vi x y ∣ vxy ∣₁))
        Va)
    (λ U V Ua Vf C ui vi →
       af₁-mono
        (λ {x} {y} uxy →
           rec! [ ∣_∣₁ ∘ inl
                , (λ ax → map (map-r (ax ,_))
                             (vi x y (Vf x y)))
                ]ᵤ
             (ui x y ∣ uxy ∣₁))
        Ua)
    λ U V Ul Vl C ui vi →
       AF₁lift λ a →
       af₁-mono
         {R = λ x y → ((C x y ⊎₁ A x × B x) ⊎₁ C a x) ⊎₁ A a × B a}
         (rec! [ map (map-r (∣_∣₁ ∘ inl))
               , ∣_∣₁ ∘ inr ∘ ∣_∣₁ ∘ inr ]ᵤ)
         (af₁-zero-inter
            (af₁-mono
               (rec! [ map (map-l (map (map-l (∣_∣₁ ∘ inl))))
                     , ∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl  ∘ ∣_∣₁ ∘ inr ]ᵤ)
               (Ul a (λ x y → (C x y ⊎₁ C a x) ⊎₁ A a)
                     (λ x y → rec! [ map (map-l (∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl)) ∘ ui x y ∘ ∣_∣₁
                                   , ∣_∣₁ ∘ inl ∘ map (map-l (∣_∣₁ ∘ inr)) ∘ ui a x ∘ ∣_∣₁ ]ᵤ)
                     (λ x y → map (map-l (∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl)) ∘ vi x y)))
            (af₁-mono
               (rec! [ map (map-l (map (map-l (∣_∣₁ ∘ inl))))
                     , ∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl  ∘ ∣_∣₁ ∘ inr ]ᵤ)
               (Vl a (λ x y → (C x y ⊎₁ C a x) ⊎₁ B a)
                     (λ x y → map (map-l (∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl)) ∘ ui x y)
                     λ x y → rec! [ map (map-l (∣_∣₁ ∘ inl ∘ ∣_∣₁ ∘ inl)) ∘ vi x y ∘ ∣_∣₁
                                  , ∣_∣₁ ∘ inl ∘ map (map-l (∣_∣₁ ∘ inr)) ∘ vi a x ∘ ∣_∣₁ ]ᵤ)))

af₁-one-inter : ∀ {ℓ ℓ′} {X : 𝒰 ℓ} {A B : X → 𝒰 ℓ′} {R : X → X → 𝒰 ℓ′}
              → AF₁ (λ x y → R x y ⊎₁ A x)
              → AF₁ (λ x y → R x y ⊎₁ B x)
              → AF₁ (λ x y → R x y ⊎₁ A x × B x)
af₁-one-inter {ℓ} {ℓ′} {R} afa afb =
  af₁-one-inter-rec
    afa afb
    R
    (λ x y → proj!) (λ x y → proj!)

-- TODO generalize to different levels on R & T ?
af₁-inter : ∀ {ℓ ℓ′} {X : 𝒰 ℓ} {R T : X → X → 𝒰 ℓ′}
          → AF₁ R
          → AF₁ T
          → AF₁ (λ x y → ∥ R x y ∥₁ × ∥ T x y ∥₁)
af₁-inter =
  af₁-double-ind
    {P = λ U V → AF₁ (λ x y → ∥ U x y ∥₁ × ∥ V x y ∥₁)}
    (λ R T → hlevel 1)
    (λ U V Uf Va → af₁-mono (λ {x} {y} vxy → Uf x y , ∣ vxy ∣₁) Va)
    (λ U V Ua Vf → af₁-mono (λ {x} {y} uxy → ∣ uxy ∣₁ , Vf x y) Ua)
    (λ U V Ul Vl →
      AF₁lift λ a →
        af₁-one-inter
         -- TODO prettify
          (af₁-mono (λ where (u , vxy) → rec! [ (λ uxy → ∣ inl (∣ uxy ∣₁ , vxy) ∣₁)
                                              , (λ uax → ∣ inr ∣ uax ∣₁ ∣₁) ]ᵤ u)
                    (Ul a))
          (af₁-mono (λ where (uxy , v) → rec! [ (λ vxy → ∣ inl (uxy , ∣ vxy ∣₁) ∣₁)
                                              , (λ vax → ∣ inr ∣ vax ∣₁ ∣₁) ]ᵤ v)
                    (Vl a)))

