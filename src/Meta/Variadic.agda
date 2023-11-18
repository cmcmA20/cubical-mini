{-# OPTIONS --safe #-}
-- -vtactic.variadic:20
module Meta.Variadic where

open import Foundations.Base

open import Meta.Reflection
open import Meta.Underlying public

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Nat.Base
open import Data.Product.Base public

-- Correspondence valued in arbitrary structure
SCorr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls)
    {ℓ : Level} (U : Type ℓ) ⦃ u : Underlying U ⦄
  → Type (ℓ ⊔ ℓsup _ ls)
SCorr arity As U = Arrows arity As U

SCorr⁰ = SCorr 0
SCorr¹ = SCorr 1
SCorr² = SCorr 2
SCorr³ = SCorr 3
SCorr⁴ = SCorr 4
SCorr⁵ = SCorr 5

SPred = SCorr¹

-- Type-valued correspondence
Corr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup _ ls)
Corr arity As ℓ = SCorr arity As (Type ℓ)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3
Corr⁴ = Corr 4
Corr⁵ = Corr 5

Pred = Corr¹


Variadic¹ : Typeω
Variadic¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Corr  _ As (u .ℓ-underlying)

UnOpⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → (Type (u .ℓ-underlying) → Type (u .ℓ-underlying))
  → SCorr _ As U
  → Corr  _ As (u .ℓ-underlying)
UnOpⁿ {0}           f P = f ⌞ P ⌟⁰
UnOpⁿ {1}           f P = λ x → f ⌞ P x ⌟⁰
UnOpⁿ {suc (suc _)} f P = λ x → UnOpⁿ f (P x)

Carrierⁿ : Variadic¹
Carrierⁿ = UnOpⁿ id


Variadic-binding¹ : Typeω
Variadic-binding¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup arity ls)

Universalⁿ : Variadic-binding¹
Universalⁿ {0}                         P = ⌞ P ⌟⁰
Universalⁿ {1}           {As = A}      P = Π[ a ꞉ A ] ⌞ P a ⌟⁰
Universalⁿ {suc (suc _)} {As = A , As} P = Π[ a ꞉ A ] Universalⁿ (P a)

IUniversalⁿ : Variadic-binding¹
IUniversalⁿ {0}                         P = ⌞ P ⌟⁰
IUniversalⁿ {1}           {As = A}      P = ∀{a} → ⌞ P a ⌟⁰
IUniversalⁿ {suc (suc _)} {As = A , As} P = ∀{a} → IUniversalⁿ (P a)

Existentialⁿ : Variadic-binding¹
Existentialⁿ {0}                         P = ⌞ P ⌟⁰
Existentialⁿ {1}           {As = A}      P = Σ[ a ꞉ A ] ⌞ P a ⌟⁰
Existentialⁿ {suc (suc _)} {As = A , As} P = Σ[ a ꞉ A ] Existentialⁿ (P a)


Variadic² : Typeω
Variadic² =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ } ⦃ u : Underlying U ⦄
    {ℓ′ : Level} {V : Type ℓ′} ⦃ v : Underlying V ⦄
  → SCorr _ As U → SCorr _ As V
  → Corr  _ As (u .ℓ-underlying ⊔ v .ℓ-underlying)

BinOpⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ } ⦃ u : Underlying U ⦄
    {ℓ′ : Level} {V : Type ℓ′} ⦃ v : Underlying V ⦄
  → ( Type (u .ℓ-underlying) → Type (v .ℓ-underlying)
    → Type (u .ℓ-underlying ⊔ v .ℓ-underlying) )
  → SCorr _ As U → SCorr _ As V
  → Corr  _ As (u .ℓ-underlying ⊔ v .ℓ-underlying)
BinOpⁿ {0}           f P Q = f ⌞ P ⌟⁰ ⌞ Q ⌟⁰
BinOpⁿ {1}           f P Q = λ x → f ⌞ P x ⌟⁰ ⌞ Q x ⌟⁰
BinOpⁿ {suc (suc _)} f P Q = λ x → BinOpⁿ f (P x) (Q x)

Implⁿ : Variadic²
Implⁿ = BinOpⁿ λ A B → (A → B)

Prodⁿ : Variadic²
Prodⁿ = BinOpⁿ _×_


-- returns reflected arity, tuple of argument types, level and result type
get-arity+type : Type′ → Term × Type′
get-arity+type t = go 0 t where
  clean-var : ℕ → Term → Term
  clean-vars : ℕ → List (Arg Term) → List (Arg Term)

  -- variable references would be invalid in current context
  clean-var nbind (var v args) =
    if nbind <ᵇ suc v
       then var (v ∸ nbind) (clean-vars nbind args)
       else var v (clean-vars nbind args)
  clean-var nbind (con c args) = con c (clean-vars nbind args)
  clean-var nbind (def f args) = def f (clean-vars nbind args)
  clean-var nbind (lam v (abs s x)) = lam v (abs s (clean-var (suc nbind) x))
  clean-var nbind (pi (arg v a) (abs s b)) =
    pi (arg v (clean-var nbind a)) (abs s (clean-var (suc nbind) b))
  clean-var nbind x = x

  clean-vars nbind [] = []
  clean-vars nbind (arg ai x ∷ xs) = arg ai (clean-var nbind x) ∷ clean-vars nbind xs

  go : ℕ → Term → Term × Type′
  go nbind (def (quote Arrows) (ar v∷ l h∷ ls h∷ sig v∷ R v∷ [])) =
    let ar′ , R′ = go nbind R
    in plus-term ar′ ar , clean-var nbind R′
    -- ^ TODO swap arguments, use _+_ with better definitional equalities
  go nbind (pi (varg t) (abs _ x)) =
    let ar , R = go (suc nbind) x
    in suc-term ar , clean-var nbind R
  go nbind (pi _ (abs _ x)) = go (suc nbind) x
  go nbind (agda-sort (lit l)) = lit (nat 0) , agda-sort (lit l)
  go nbind (agda-sort (set r)) = lit (nat 0) , agda-sort (set (clean-var nbind r))
  go nbind x                   = lit (nat 0) , clean-var nbind x

-- returns inferred arity and result type
variadic-worker : Term → TC (Term × Term)
variadic-worker t = do
  ty ← (inferType t >>= reduce) >>= wait-just-a-bit
  debugPrint "tactic.variadic" 20 [ "Given type: " , termErr ty ]
  let ar , r = get-arity+type ty
  r ← wait-just-a-bit r
  debugPrint "tactic.variadic" 20
    [ "Inferred arity: " , termErr ar , "\n"
    , "Last type: " , termErr r ]
  unify ty $ def (quote Arrows)
    [ varg ar , harg unknown , harg unknown , varg unknown , varg unknown ]
  pure $ ar , r

-- returns underlying instance
variadic-instance-worker : Term → TC Term
variadic-instance-worker r = do
  solved@(meta mv _) ← new-meta (def (quote Underlying) [ harg unknown , varg r ])
    where _ → typeError [ "Could not get `Underlying` instances: " , termErr r ]
  (und ∷ []) ← getInstances mv where
    [] → typeError [ "No `Underlying `instances for ", termErr r ]
    _  → typeError [ "Multiple `Underlying` instances for ", termErr r ]
  unify solved und
  pure und

carrier-macro : Term → Term → TC ⊤
carrier-macro t hole = do
  ar , r ← variadic-worker t
  und ← variadic-instance-worker r
  unify hole $ def (quote Carrierⁿ)
    [ harg ar , harg unknown , harg unknown
    , harg unknown , harg unknown , iarg und
    , varg t ]

macro ⌞_⌟ = carrier-macro

quantifier-macro : Name → Term → Term → TC ⊤
quantifier-macro nam t hole = do
  ar , r ← variadic-worker t
  und ← variadic-instance-worker r
  unify hole $ def nam $
    [ harg ar , harg unknown , harg unknown
    , harg unknown , harg unknown , iarg und
    , varg t ]

infixr 6 Π[_] ∀[_] Σ[_]
macro
  Π[_] = quantifier-macro (quote Universalⁿ)
  ∀[_] = quantifier-macro (quote IUniversalⁿ)
  Σ[_] = quantifier-macro (quote Existentialⁿ)


binop-macro : Name → Term → Term → Term → TC ⊤
binop-macro nam p q hole = do
  par , pr ← variadic-worker p
  qar , qr ← variadic-worker q
  unify par qar
  pund ← variadic-instance-worker pr
  qund ← variadic-instance-worker qr
  unify hole $ def nam
    [ harg par , harg unknown , harg unknown
    , harg unknown , harg unknown , iarg pund
    , harg unknown , harg unknown , iarg qund
    , varg p , varg q ]

infixr -1 _→̇_
infixr 8 _×̇_
macro
  _→̇_ = binop-macro (quote Implⁿ)
  _×̇_ = binop-macro (quote Prodⁿ)
