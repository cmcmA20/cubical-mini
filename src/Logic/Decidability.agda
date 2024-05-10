{-# OPTIONS --safe #-}
module Logic.Decidability where

open import Meta.Prelude
open import Meta.Reflection.Base
open import Meta.Reflection.Neutral
open import Meta.Reflection.Signature

open import Logic.DoubleNegation

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflection.Term
open import Data.Reflects.Path
open import Data.Reflects.Properties
open import Data.Truncation.Propositional.Base as ∥-∥₁

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  n : HLevel

dec→essentially-classical : Dec A → Essentially-classical A
dec→essentially-classical = Dec.rec
  (λ a _ → a)
  (λ ¬a f → ⊥.rec $ f ¬a)

instance
  Dec-⊥ : Dec ⊥
  Dec-⊥ = no id
  {-# OVERLAPPING Dec-⊥ #-}

  Dec-⊤ : Dec ⊤
  Dec-⊤ = yes tt
  {-# OVERLAPPING Dec-⊤ #-}

  Dec-× : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A × B)
  Dec-× ⦃ da ⦄    ⦃ db ⦄ .does = da .does and db .does
  Dec-× ⦃ no ¬a ⦄ ⦃ db ⦄ .proof = ofⁿ $ ¬a ∘ fst
  Dec-× ⦃ yes a ⦄ ⦃ no ¬b ⦄ .proof = ofⁿ $ ¬b ∘ snd
  Dec-× ⦃ yes a ⦄ ⦃ yes b ⦄ .proof = ofʸ (a , b)

  Dec-fun : ⦃ da : Dec A ⦄ → ⦃ db : Dec B ⦄ → Dec (A → B)
  Dec-fun ⦃ da ⦄    ⦃ db ⦄ .does = not (da .does) or db .does
  Dec-fun ⦃ no ¬a ⦄ ⦃ db ⦄ .proof = ofʸ $ λ a → ⊥.rec $ ¬a a
  Dec-fun ⦃ yes a ⦄ ⦃ no ¬b ⦄ .proof = ofⁿ $ ¬b ∘ (_$ a)
  Dec-fun ⦃ yes a ⦄ ⦃ yes b ⦄ .proof = ofʸ λ _ → b
  {-# OVERLAPPABLE Dec-fun #-}

  Dec-¬ : ⦃ da : Dec A ⦄ → Dec (¬ A)
  Dec-¬ ⦃ da ⦄ .does = not (da .does)
  Dec-¬ ⦃ yes a ⦄ .proof = ofⁿ (_$ a)
  Dec-¬ ⦃ no ¬a ⦄ .proof = ofʸ ¬a

  Dec-lift : ⦃ da : Dec A ⦄ → Dec (Lift ℓ A)
  Dec-lift ⦃ da ⦄ .does = da .does
  Dec-lift ⦃ yes a ⦄ .proof = ofʸ (lift a)
  Dec-lift ⦃ no ¬a ⦄ .proof = ofⁿ (¬a ∘ lower)

  Dec-∥-∥₁ : ⦃ da : Dec A ⦄ → Dec ∥ A ∥₁
  Dec-∥-∥₁ ⦃ da ⦄ .does = da .does
  Dec-∥-∥₁ ⦃ yes a ⦄ .proof = ofʸ ∣ a ∣₁
  Dec-∥-∥₁ ⦃ no ¬a ⦄ .proof = ofⁿ $ rec! ¬a
  {-# OVERLAPPABLE Dec-∥-∥₁ #-}

  Dec-universe : Dec (Type ℓ)
  Dec-universe = yes (Lift _ ⊤)

  Dec-refl : ∀ {x : A} → Dec (x ＝ x)
  Dec-refl = yes refl
  {-# OVERLAPPING Dec-refl #-}


-- Decidability of a generalized predicate
Decidableⁿ : Variadic-binding¹
Decidableⁿ {arity} P = ∀[ mapⁿ arity Dec ⌞ P ⌟ ]

macro
  Decidable : Term → Term → TC ⊤
  Decidable t hole = do
    ar , r ← variadic-worker t
    und ← variadic-instance-worker r
    unify hole
      $   it Decidableⁿ ##ₕ ar ##ₕ unknown ##ₕ unknown
      ##ₕ unknown ##ₕ unknown ##ᵢ und ##ₙ t

-- Decision procedure
DProc
  : (arity : ℕ)
    {ls : Levels arity} (As : Types _ ls)
  → Type (ℓsup arity ls)
DProc arity As = Arrows arity As Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3
DProc⁴ = DProc 4
DProc⁵ = DProc 5

-- Evidence of a correspondence `P` being reflected by a decision procedure
Reflectsⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U → DProc _ As → Type (u .ℓ-underlying ⊔ ℓsup _ ls)
Reflectsⁿ {0}                         P d = Reflects⁰ ⌞ P ⌟⁰ d
Reflectsⁿ {1}           {As = A}      P d = Π[ x ꞉ A ] Reflectsⁿ (P x) (d x)
Reflectsⁿ {suc (suc _)} {As = A , As} P d = Π[ x ꞉ A ] Reflectsⁿ (P x) (d x)

reflectsⁿ-is-of-hlevel
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {h : HLevel} {P : SCorr _ As U} {d : DProc _ As}
  → Π[ mapⁿ arity (is-of-hlevel (suc h)) ⌞ P ⌟ ]
  → is-of-hlevel (suc h) (Reflectsⁿ P d)
reflectsⁿ-is-of-hlevel {0} = reflects-is-of-hlevel _
reflectsⁿ-is-of-hlevel {1} hl = Π-is-of-hlevel _ λ _ →
  reflects-is-of-hlevel _ (hl _)
reflectsⁿ-is-of-hlevel {suc (suc arity)} hl = Π-is-of-hlevel _ λ _ →
  reflectsⁿ-is-of-hlevel (hl _)

macro
  Reflects : Term → Term → Term → TC ⊤
  Reflects c d hole = do
    car , r ← variadic-worker c
    dar , _ ← variadic-worker d
    unify car dar
    und ← variadic-instance-worker r
    unify hole
      $   it Reflectsⁿ ##ₕ car ##ₕ unknown ##ₕ unknown
      ##ₕ unknown ##ₕ unknown ##ᵢ und ##ₙ c ##ₙ d

reflectsⁿ-bool-inj
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {P : SCorr _ As U} {d₁ d₂ : DProc _ As}
  → Reflects P d₁ → Reflects P d₂
  → d₁ ＝ d₂
reflectsⁿ-bool-inj {0} = reflects-bool-inj
reflectsⁿ-bool-inj {1} r₁ r₂ = fun-ext λ x → reflects-bool-inj (r₁ x) (r₂ x)
reflectsⁿ-bool-inj {suc (suc _)} r₁ r₂ = fun-ext λ x → reflectsⁿ-bool-inj (r₁ x) (r₂ x)

reflects→decidable
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {P : SCorr _ As U} {d : DProc _ As}
  → Reflects P d → Decidable P
reflects→decidable {0}          {d} p     = d because p
reflects→decidable {1}          {d} f {x} = d x because f x
reflects→decidable {suc (suc _)}    f {x} = reflects→decidable (f x)

-- TODO move
-- opaque
--   unfolding is-of-hlevel
--   decidable₁→reflects!
--     : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
--       {ℓ : Level} {P : Rel _ As ℓ}
--     → Decidable P → ∃![ d ꞉ DProc _ As ] Reflects P d
--   decidable₁→reflects! {0} p =
--       (p .does , p .proof)
--     , λ z → Σ-prop-path! $ reflects-bool-inj (z .snd) (p .proof) ⁻¹
--   decidable₁→reflects! {1} f =
--       (does ∘ f  , proof ∘ f)
--     , λ z → Σ-prop-path! $ fun-ext λ x → reflects-bool-inj (z .snd x) (f x .proof) ⁻¹
--   decidable₁→reflects! {suc (suc arity)} {As} {ℓ} {P} f =
--     let ih = decidable₁→reflects!
--     in ((λ x → ih (f x) .fst .fst) , λ x → ih (f x) .fst .snd)
--       , λ z → Σ-prop-path (λ _ → reflectsⁿ-is-of-hlevel {arity = suc (suc arity)} {h = 0} $ corr→is-of-hlevelⁿ {arity = suc (suc arity)})
--                           (fun-ext λ x → let u = ih (f x) .snd (z .fst x , z .snd x) in ap fst u)
