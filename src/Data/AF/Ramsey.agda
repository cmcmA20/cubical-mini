{-# OPTIONS --safe #-}
module Data.AF.Ramsey where

open import Foundations.Base
open Variadics _

open import Data.AF.Base
open import Data.Sum.Base

{-
private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′
-}

af-double-ind : ∀ {ℓ ℓ′ ℓ″} {A : 𝒰 ℓ} {P : (A → A → 𝒰 ℓ′) → (A → A → 𝒰 ℓ′) → 𝒰 ℓ″}
              → ((R T : A → A → 𝒰 ℓ′) → (∀ x y → R x y) → AF T → P R T)
              → ((R T : A → A → 𝒰 ℓ′) → AF R → (∀ x y → T x y) → P R T)
              → ((R T : A → A → 𝒰 ℓ′) → (∀ x → P (R ↑ x) T) → (∀ x → P R (T ↑ x)) → P R T)
              → {R T : A → A → 𝒰 ℓ′} → AF R → AF T → P R T
af-double-ind Hl Hr H2    (AFfull afr) at              =
  Hl _ _ afr at
af-double-ind Hl Hr H2 ar@(AFlift _)      (AFfull aft) =
  Hr _ _ ar aft
af-double-ind Hl Hr H2 ar@(AFlift alr) at@(AFlift alt) =
  H2 _ _
   (λ x → af-double-ind Hl Hr H2 (alr x) at)
   (λ x → af-double-ind Hl Hr H2 ar (alt x))

af-zero-inter-rec : ∀ {ℓ ℓ′ ℓ″} {X : 𝒰 ℓ} {A B : 𝒰 ℓ′} {R T : X → X → 𝒰 ℓ″}
                  → AF R → AF T
                  → (C : X → X → 𝒰 ℓ′)
                  → (∀ x y → R x y → C x y ⊎ A)
                  → (∀ x y → T x y → C x y ⊎ B)
                  → AF (λ x y → C x y ⊎ A × B)
af-zero-inter-rec {ℓ′} {X} {A} {B} =
  af-double-ind
    {P = λ U V → (C : X → X → 𝒰 ℓ′)
               → (∀ x y → U x y → C x y ⊎ A)
               → (∀ x y → V x y → C x y ⊎ B)
               → AF (λ x y → C x y ⊎ A × B)}
    (λ U V Uf Va C ui vi →
       af-mono (λ {x} {y} →
                   [ inl
                   , (λ b → [ inl
                            , (λ a → inr (a , b))
                            ]ᵤ (ui x y (Uf x y)))
                   ]ᵤ ∘ vi x y)
               Va)
    (λ U V Ua Vf C ui vi →
       af-mono (λ {x} {y} →
                   [ inl
                   , (λ a → [ inl
                            , (λ b → inr (a , b))
                            ]ᵤ (vi x y (Vf x y)))
                   ]ᵤ ∘ ui x y)
               Ua)
    λ U V Ul Vl C ui vi →
       AFlift λ a →
       af-mono {R = λ x y → (C x y ⊎ C a x) ⊎ A × B}
          [ [ inl ∘ inl , inr ∘ inl ]ᵤ , inr ∘ inr ]ᵤ
          (Ul a (C ↑ a)
             (λ x y → [ [ inl ∘ inl , inr ]ᵤ ∘ ui x y
                      , [ inl ∘ inr , inr ]ᵤ ∘ ui a x ]ᵤ)
             (λ x y → [ inl ∘ inl , inr ]ᵤ ∘ vi x y))

af-zero-inter : ∀ {ℓ ℓ′} {X : 𝒰 ℓ} {A B : 𝒰 ℓ′} {R : X → X → 𝒰 ℓ′}
              → AF (λ x y → R x y ⊎ A)
              → AF (λ x y → R x y ⊎ B)
              → AF (λ x y → R x y ⊎ A × B)
af-zero-inter {R} afa afb = af-zero-inter-rec afa afb R (λ x y → id) (λ x y → id)

af-one-inter-rec : ∀ {ℓ ℓ′ ℓ″} {X : 𝒰 ℓ} {A B : X → 𝒰 ℓ′} {R T : X → X → 𝒰 ℓ″}
                  → AF R → AF T
                  → (C : X → X → 𝒰 ℓ′)
                  → (∀ x y → R x y → C x y ⊎ A x)
                  → (∀ x y → T x y → C x y ⊎ B x)
                  → AF (λ x y → C x y ⊎ A x × B x)
af-one-inter-rec {ℓ′} {X} {A} {B} =
  af-double-ind
    {P = λ U V → (C : X → X → 𝒰 ℓ′)
               → (∀ x y → U x y → C x y ⊎ A x)
               → (∀ x y → V x y → C x y ⊎ B x)
               → AF (λ x y → C x y ⊎ A x × B x)}
    (λ U V Uf Va C ui vi →
       af-mono (λ {x} {y} → [ inl
                            , (λ bx → [ inl
                                      , (λ ax → inr (ax , bx))
                                      ]ᵤ (ui x y (Uf x y)))
                            ]ᵤ ∘ (vi x y)) Va)
    (λ U V Ua Vf C ui vi →
       af-mono (λ {x} {y} → [ inl
                            , (λ ax → [ inl
                                      , (λ bx → inr (ax , bx))
                                      ]ᵤ (vi x y (Vf x y)))
                            ]ᵤ ∘ (ui x y)) Ua)
    (λ U V Ul Vl C ui vi →
       AFlift λ a →
       af-mono {R = λ x y → ((C x y ⊎ A x × B x) ⊎ C a x) ⊎ A a × B a}
          [ [ [ inl ∘ inl , inl ∘ inr ]ᵤ , inr ∘ inl ]ᵤ , inr ∘ inr ]ᵤ
          (af-zero-inter
             (af-mono
               [ [ [ inl ∘ inl ∘ inl , inl ∘ inr ]ᵤ , inr ]ᵤ , inl ∘ inl ∘ inr ]ᵤ
               (Ul a (λ x y → (C x y ⊎ C a x) ⊎ A a)
                   (λ x y → [ [ inl ∘ inl ∘ inl , inr ]ᵤ ∘ ui x y
                            , [ inl ∘ inl ∘ inr , inl ∘ inr ]ᵤ ∘ ui a x ]ᵤ)
                   λ x y → [ inl ∘ inl ∘ inl , inr ]ᵤ ∘ vi x y))
             (af-mono
               [ [ [ inl ∘ inl ∘ inl , inl ∘ inr ]ᵤ , inr ]ᵤ , inl ∘ inl ∘ inr ]ᵤ
               (Vl a (λ x y → (C x y ⊎ C a x) ⊎ B a)
                   (λ x y → [ inl ∘ inl ∘ inl , inr ]ᵤ ∘ ui x y)
                   λ x y → [ [ inl ∘ inl ∘ inl , inr ]ᵤ ∘ vi x y
                            , [ inl ∘ inl ∘ inr , inl ∘ inr ]ᵤ ∘ vi a x ]ᵤ)))
                            )

af-one-inter : ∀ {ℓ ℓ′} {X : 𝒰 ℓ} {A B : X → 𝒰 ℓ′} {R : X → X → 𝒰 ℓ′}
              → AF (λ x y → R x y ⊎ A x)
              → AF (λ x y → R x y ⊎ B x)
              → AF (λ x y → R x y ⊎ A x × B x)
af-one-inter {ℓ} {ℓ′} {R} afa afb =
  af-one-inter-rec
    afa afb
    R
    (λ x y → id) (λ x y → id)

-- TODO generalize to different levels on R & T ?
af-inter : ∀ {ℓ ℓ′} {X : 𝒰 ℓ} {R T : X → X → 𝒰 ℓ′}
         → AF R
         → AF T
         → AF (λ x y → R x y × T x y)
af-inter =
  af-double-ind
    {P = λ U V → AF (λ x y → U x y × V x y)}
    (λ U V Uf Va → af-mono (λ {x} {y} vxy → Uf x y , vxy) Va)
    (λ U V Ua Vf → af-mono (λ {x} {y} uxy → uxy , Vf x y) Ua)
    (λ U V Ul Vl →
      AFlift λ a →
      af-one-inter
        (af-mono (λ where
                      (inl uxy , vxy) → inl (uxy , vxy)
                      (inr uax , _  ) → inr uax)
                 (Ul a))
        (af-mono (λ where
                      (uxy , inl vxy) → inl (uxy , vxy)
                      (_   , inr vax) → inr vax)
                 (Vl a)))
