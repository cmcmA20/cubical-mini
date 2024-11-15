{-# OPTIONS --safe #-}
module Data.AF.Examples where

open import Foundations.Base
open import Foundations.HLevel

open import Data.Empty.Base
open import Data.Unit.Base
open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Reflects.Base
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Star.Base
open import Data.Plus.Base
open import Data.Plus.Properties
open import Data.Acc.Base
open import Data.AF.Base
open import Data.AF.Ramsey
open import Data.AF.WF
open import Data.AF.Constructions

open import Order.Base
open import Order.Strict
open import Order.Constructions.Product
open import Order.Constructions.Lex
open import Order.Constructions.Nat

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  R T : A → A → 𝒰 ℓ′

R× : ℕ × ℕ → ℕ × ℕ → 𝒰
R× = (ℕₚ × ℕₚ) .Poset._≤_

A× : AF R×
A× = af-× af-≤ af-≤

-- flex

Tfl : ℕ × ℕ → ℕ × ℕ → 𝒰
Tfl = (ℕₛ <×< ℕₛ) .StrictPoset._<_

Tfl-empty-intersect : ∀ {x₁ x₂ y₁ y₂}
                    → Plus Tfl (x₁ , x₂) (y₁ , y₂)
                    → R× (y₁ , y₂) (x₁ , x₂)
                    → ⊥
Tfl-empty-intersect p (y₁≤x₁ , y₂≤x₂) =
  [ (λ            x₁<y₁  → <→≱ x₁<y₁ y₁≤x₁)
  , (λ where (_ , x₂<y₂) → <→≱ x₂<y₂ y₂≤x₂)
  ]ᵤ (plus-fold1 (record { _∙_ = (ℕₛ <×< ℕₛ) .StrictPoset.<-trans }) p)

-- or directly by induction
Tfl-empty-intersect′ : ∀ {x₁ x₂ y₁ y₂}
                    → Plus Tfl (x₁ , x₂) (y₁ , y₂)
                    → R× (y₁ , y₂) (x₁ , x₂)
                    → ⊥
Tfl-empty-intersect′ [ inl x<y₁ ]⁺       (y≤x₁ , y≤x₂) = <→≱ x<y₁ y≤x₁
Tfl-empty-intersect′ [ inr (e , x<y₂) ]⁺ (y≤x₁ , y≤x₂) = <→≱ x<y₂ y≤x₂
Tfl-empty-intersect′ (h ◅⁺ p)            (y≤x₁ , y≤x₂) =
  [ ≤→≯ (plus-fold1 Trans-≤ (plus-map [ <→≤ , =→≤ ∘ fst ]ᵤ p) ∙ y≤x₁)
  , (λ where (e , x<w₂) → Tfl-empty-intersect′ p (y≤x₁ ∙ =→≤ e , y≤x₂ ∙ <→≤ x<w₂))
  ]ᵤ h

flex : ℕ × ℕ → ℕ
flex =
  to-induction (AF→WF A× Tfl-empty-intersect) (λ _ → ℕ)
    λ x ih → go (x .fst) (x .snd) λ a b → ih (a , b)
  where
  go : ∀ x y → (∀ a b → Tfl (a , b) (x , y) → ℕ) → ℕ
  go  zero    _      _  = 1
  go (suc _)  zero   _  = 1
  go (suc x) (suc y) ih = ih x (2 + y) (inl <-ascend) + ih (1 + x) y (inr (refl , <-ascend))

-- grok

Tgr : ℕ × ℕ → ℕ × ℕ → 𝒰
Tgr (x₁ , x₂) (y₁ , y₂) = ((x₁ ≤ y₂) × (x₂ < y₂)) ⊎ ((x₂ < y₁) × (x₁ < y₁))

Tgr-trans : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
          → Tgr (x₁ , x₂) (y₁ , y₂)
          → Tgr (y₁ , y₂) (z₁ , z₂)
          → Tgr (x₁ , x₂) (z₁ , z₂)
Tgr-trans (inl (x₁≤y₂ , x₂<y₂)) (inl (_     , y₂<z₂)) = inl (x₁≤y₂ ∙ <→≤ y₂<z₂   , <-trans x₂<y₂ y₂<z₂)
Tgr-trans (inl (x₁≤y₂ , x₂<y₂)) (inr (y₂<z₁ , _    )) = inr (<-trans x₂<y₂ y₂<z₁ , ≤-<-trans x₁≤y₂ y₂<z₁)
Tgr-trans (inr (x₂<y₁ , x₁<y₁)) (inl (y₁≤z₂ , _    )) = inl (<→≤ x₁<y₁ ∙ y₁≤z₂   , <-≤-trans x₂<y₁ y₁≤z₂)
Tgr-trans (inr (x₂<y₁ , x₁<y₁)) (inr (_     , y₁<z₁)) = inr (<-trans x₂<y₁ y₁<z₁ , <-trans x₁<y₁ y₁<z₁)

Tgr-empty-intersect : ∀ {x₁ x₂ y₁ y₂}
                    → Plus Tgr (x₁ , x₂) (y₁ , y₂)
                    → R× (y₁ , y₂) (x₁ , x₂)
                    → ⊥
Tgr-empty-intersect p (y≤x₁ , y≤x₂) =
  [ (λ where (_ , x<y₂) → <→≱ x<y₂ y≤x₂)
  , (λ where (_ , x<y₁) → <→≱ x<y₁ y≤x₁)
  ]ᵤ (plus-fold1 (record { _∙_ = Tgr-trans }) p)

grok : ℕ × ℕ → ℕ
grok =
  to-induction (AF→WF A× Tgr-empty-intersect) (λ _ → ℕ)
    λ x ih → go (x .fst) (x .snd) λ a b → ih (a , b)
  where
  go : ∀ x y → (∀ a b → Tgr (a , b) (x , y) → ℕ) → ℕ
  go  zero    _      _  = 1
  go (suc _)  zero   _  = 1
  go (suc x) (suc y) ih = ih (1 + y) y (inl (refl , <-ascend)) + ih x x (inr (<-ascend , <-ascend))

-- flip1

Tf1 : ℕ × ℕ → ℕ × ℕ → 𝒰
Tf1 (x₁ , x₂) (y₁ , y₂) = (x₁ ≤ y₂) × (x₂ < y₁)

Rf1 : ℕ × ℕ → ℕ × ℕ → 𝒰
Rf1 (x₁ , x₂) (y₁ , y₂) = x₁ + x₂ ≤ y₁ + y₂

Tf1-intersection-empty : ∀ {x₁ x₂ y₁ y₂}
                       → Plus Tf1 (x₁ , x₂) (y₁ , y₂)
                       → Rf1 (y₁ , y₂) (x₁ , x₂)
                       → ⊥
Tf1-intersection-empty {x₁} {x₂} {y₁} {y₂} p y₁₂≤x₁₂ =
  ≤→≯ y₁₂≤x₁₂ $
  plus-fold1 {R = _<_} (record { _∙_ = <-trans}) $
  plus-map (λ where {a = a₁ , a₂} {b = b₁ , b₂} (a₁≤b₂ , a₂<b₁) →
                      subst (a₁ + a₂ <_) (+-comm b₂ b₁) $ ≤-<-+ a₁≤b₂ a₂<b₁) p

flip1 : ℕ × ℕ → ℕ
flip1 =
  to-induction
    (AF→WF (af-comap (λ where (x , y) → x + y) af-≤) Tf1-intersection-empty)
    (λ _ → ℕ)
    λ x ih → go (x .fst) (x .snd) λ a b → ih (a , b)
  where
  go : ∀ x y → (∀ a b → Tf1 (a , b) (x , y) → ℕ) → ℕ
  go  zero    _      _  = 1
  go (suc _)  zero   _  = 1
  go (suc x) (suc y) ih = ih (1 + y) x (refl , <-ascend)

-- gnlex

Tgn : ℕ × ℕ → ℕ × ℕ → 𝒰
Tgn (x₁ , x₂) (y₁ , y₂) = (x₁ ＝ y₂) × ((x₂ < y₂) ⊎ (x₂ < y₁))

T2-inv : ∀ {x₁ x₂ y₁ y₂}
       → pow 2 Tgn (x₁ , x₂) (y₁ , y₂)
       → ((x₁ < y₁) × (x₂ < y₁)) ⊎ ((x₂ < y₂) × (x₁ < y₂)) ⊎ ((x₁ < y₁) × (x₂ < y₂))
T2-inv ((z₁ , z₂) , (exz , inl x<z) , (w₁ , w₂) , (ezw , inl z<w) , lift ewy) =
  inr $ inl ( <-≤-trans x<z (<→≤ z<w ∙ =→≤ (ap snd ewy))
            , ≤-<-trans (=→≤ exz) (<-≤-trans z<w (=→≤ (ap snd ewy))))
T2-inv ((z₁ , z₂) , (exz , inl x<z) , (w₁ , w₂) , (ezw , inr z<w) , lift ewy) =
  inl       ( ≤-<-trans (=→≤ exz) (<-≤-trans z<w (=→≤ (ap fst ewy)))
            , <-≤-trans x<z (<→≤ z<w ∙ =→≤ (ap fst ewy)))
T2-inv ((z₁ , z₂) , (exz , inr x<z) , (w₁ , w₂) , (ezw , inl z<w) , lift ewy) =
  inr $ inl ( <-≤-trans x<z (=→≤ (ezw ∙ ap snd ewy))
            , ≤-<-trans (=→≤ exz) (<-≤-trans z<w (=→≤ (ap snd ewy))))
T2-inv ((z₁ , z₂) , (exz , inr x<z) , (w₁ , w₂) , (ezw , inr z<w) , lift ewy) =
  inr $ inr ( ≤-<-trans (=→≤ exz) (<-≤-trans z<w (=→≤ (ap fst ewy)))
            , <-≤-trans x<z (=→≤ (ezw ∙ ap snd ewy)))

T2-plus-inv : ∀ {x₁ x₂ y₁ y₂}
            → Plus (pow 2 Tgn) (x₁ , x₂) (y₁ , y₂)
            → ((x₁ < y₁) × (x₂ < y₁)) ⊎ ((x₂ < y₂) × (x₁ < y₂)) ⊎ ((x₁ < y₁) × (x₂ < y₂))
T2-plus-inv [ p2 ]⁺    = T2-inv p2
T2-plus-inv (_◅⁺_ {y = (w₁ , w₂)} p2 pl) with T2-inv p2 | T2-plus-inv pl
... | inl      (x<w₁ , x<w₂)  | inl      (w<y₁ , _   )  = inl       (<-trans x<w₁ w<y₁ , <-trans x<w₂ w<y₁)
... | inl      (x<w₁ , x<w₂)  | inr (inl (_    , w<y₁)) = inr $ inl (<-trans x<w₂ w<y₁ , <-trans x<w₁ w<y₁)
... | inl      (x<w₁ , x<w₂)  | inr (inr (w<y₁ , _   )) = inl       (<-trans x<w₁ w<y₁ , <-trans x<w₂ w<y₁)
... | inr (inl (x<w₂ , x<w₁)) | inl      (_    , w<y₂)  = inl       (<-trans x<w₁ w<y₂ , <-trans x<w₂ w<y₂)
... | inr (inl (x<w₂ , x<w₁)) | inr (inl (w<y₂ , _   )) = inr $ inl (<-trans x<w₂ w<y₂ , <-trans x<w₁ w<y₂)
... | inr (inl (x<w₂ , x<w₁)) | inr (inr (_    , w<y₂)) = inr $ inl (<-trans x<w₂ w<y₂ , <-trans x<w₁ w<y₂)
... | inr (inr (x<w₁ , x<w₂)) | inl      (w<y₁ , w<y₂)  = inl       (<-trans x<w₁ w<y₁ , <-trans x<w₂ w<y₂)
... | inr (inr (x<w₁ , x<w₂)) | inr (inl (w<y₂ , w<y₁)) = inr $ inl (<-trans x<w₂ w<y₂ , <-trans x<w₁ w<y₁)
... | inr (inr (x<w₁ , x<w₂)) | inr (inr (w<y₁ , w<y₂)) = inr $ inr (<-trans x<w₁ w<y₁ , <-trans x<w₂ w<y₂)

Tgn-plus-decompose : ∀ {x₁ x₂ y₁ y₂}
                   → Plus Tgn (x₁ , x₂) (y₁ , y₂)
                   → Tgn (x₁ , x₂) (y₁ , y₂)
                   ⊎ Plus (pow 2 Tgn) (x₁ , x₂) (y₁ , y₂)
                   ⊎ (Σ[ (z₁ , z₂) ꞉ ℕ × ℕ ] (Tgn (x₁ , x₂) (z₁ , z₂)) × (Plus (pow 2 Tgn) (z₁ , z₂) (y₁ , y₂)))
Tgn-plus-decompose                     [ txy ]⁺                       = inl txy
Tgn-plus-decompose {x₁} {x₂} {y₁} {y₂} (_◅⁺_ {y = (w₁ , w₂)} txw pwy) with Tgn-plus-decompose pwy
... | inl twy                           = inr $ inl [ (w₁ , w₂) , txw , (y₁ , y₂) , twy , lift refl ]⁺
... | inr (inl p)                       = inr $ inr ((w₁ , w₂) , txw , p)
... | inr (inr ((z₁ , z₂) , twz , pzy)) = inr $ inl (((w₁ , w₂) , txw , (z₁ , z₂) , twz , lift refl) ◅⁺ pzy)

Tgn-empty-intersect : ∀ {x₁ x₂ y₁ y₂}
                    → Plus Tgn (x₁ , x₂) (y₁ , y₂)
                    → R× (y₁ , y₂) (x₁ , x₂)
                    → ⊥
Tgn-empty-intersect p (y≤x₁ , y≤x₂) =
  [ (λ where
         (e , inl x₂<y₂) → <→≱ x₂<y₂ y≤x₂
         (e , inr x₂<y₁) → <→≱ x₂<y₁ (y≤x₁ ∙ =→≤ e ∙ y≤x₂))
  , [ [ (λ where (x₁<y₁ , _) → <→≱ x₁<y₁ y≤x₁)
      , [ (λ where (x₂<y₂ , _) → <→≱ x₂<y₂ y≤x₂)
        , (λ where (x₁<y₁ , _) → <→≱ x₁<y₁ y≤x₁)
        ]ᵤ
      ]ᵤ ∘ T2-plus-inv
    , (λ where ((z₁ , z₂) , (e , txz) , pzy) →
                  [ (λ where (_ , z₂<y₁) → <→≱ z₂<y₁ (y≤x₁ ∙ =→≤ e))
                  , [ (λ x₂<z₂ → λ where
                                    (inl (z₂<y₂ , _    )) → ≤→≯ y≤x₂ (<-trans x₂<z₂ z₂<y₂)
                                    (inr (_     , z₂<y₂)) → ≤→≯ y≤x₂ (<-trans x₂<z₂ z₂<y₂))
                    , (λ x₂<z₁ → λ where
                                    (inl (_     , z₁<y₂)) → ≤→≯ y≤x₂ (<-trans x₂<z₁ z₁<y₂)
                                    (inr (z₁<y₁ , z₂<y₂)) → ≤→≯ (y≤x₁ ∙ =→≤ e) (<-trans z₂<y₂ (≤-<-trans y≤x₂ (<-trans x₂<z₁ z₁<y₁))))
                    ]ᵤ txz
                  ]ᵤ (T2-plus-inv pzy))
    ]ᵤ
  ]ᵤ (Tgn-plus-decompose p)

gnlex : ℕ × ℕ → ℕ
gnlex =
  to-induction (AF→WF A× Tgn-empty-intersect) (λ _ → ℕ)
    λ x ih → go (x .fst) (x .snd) λ a b → ih (a , b)
  where
  go : ∀ x y → (∀ a b → Tgn (a , b) (x , y) → ℕ) → ℕ
  go  zero    _      _  = 1
  go (suc _)  zero   _  = 1
  go (suc x) (suc y) ih = ih (1 + y) y (refl , inl <-ascend) + ih (1 + y) x (refl , inr <-ascend)

{-
-- fsum

Tfs : ℕ ⊎ ℕ → ℕ ⊎ ℕ → 𝒰
Tfs x y = (Σ[ z ꞉ ℕ ] (x ＝ inr (2 + z)) × (y ＝ inl (1 + z)))
        ⊎ (Σ[ z ꞉ ℕ ] (x ＝ inl (z ∸ 2)) × (y ＝ inr z))

Rfs : ℕ ⊎ ℕ → ℕ ⊎ ℕ → 𝒰
Rfs = ↑⊎ _≤_ _≤_

fsum : ℕ ⊎ ℕ → ℕ
fsum =
  to-induction
    (AF→WF {R = Rfs} {T = Tfs}
           (af-⊎ af-≤ af-≤)
           {!!})
    (λ _ → ℕ)
    go
  where
  go : (x : ℕ ⊎ ℕ) → ((y : ℕ ⊎ ℕ) → Tfs y x → ℕ) → ℕ
  go (inl zero)    ih = 1
  go (inl (suc x)) ih = ih (inr (2 + x)) (inl (x , (refl , refl)))
  go (inr x)       ih = ih (inl (x ∸ 2)) (inr (x , (refl , refl)))
-}

