{-# OPTIONS --safe #-}
-- -vtactic.variadic:20
module Meta.Variadic where

open import Foundations.Base
  hiding (_$_)

open import Meta.Reflection.Base
open import Meta.Reflection.Subst
open import Meta.Underlying public

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.HVec.Base public
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.List.Operations
open import Data.Nat.Base
open import Data.Reflection.Abs
open import Data.Reflection.Argument
open import Data.Reflection.Error
open import Data.Reflection.Fixity
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Term
open import Data.Sum.Base

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
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Corr  _ As (u .ℓ-underlying)

Lift-op¹⃑ⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → ({ℓᵃ : Level} → Type ℓᵃ → Type ℓᵃ)
  → SCorr _ As U
  → Corr  _ As (u .ℓ-underlying)
Lift-op¹⃑ⁿ {0}           f P = f ⌞ P ⌟⁰
Lift-op¹⃑ⁿ {1}           f P = λ x → f ⌞ P x ⌟⁰
Lift-op¹⃑ⁿ {suc (suc _)} f P = λ x → Lift-op¹⃑ⁿ f (P x)

Carrierⁿ : Variadic¹
Carrierⁿ = Lift-op¹⃑ⁿ id

Negⁿ : Variadic¹
Negⁿ = Lift-op¹⃑ⁿ ¬_


Variadic-binding¹ : Typeω
Variadic-binding¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup _ ls)

Quantⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → (∀ {ℓᵃ ℓᵇ} (A : Type ℓᵃ) → (A → Type ℓᵇ) → Type (ℓᵃ ⊔ ℓᵇ))
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup _ ls)
Quantⁿ {0}           Q T = ⌞ T ⌟⁰
Quantⁿ {1}           Q T = Q _ λ x → ⌞ T x ⌟⁰
Quantⁿ {suc (suc _)} Q T = Q _ λ x → Quantⁿ Q (T x)

Universalⁿ : Variadic-binding¹
Universalⁿ = Quantⁿ Π-syntax

IUniversalⁿ : Variadic-binding¹
IUniversalⁿ = Quantⁿ ∀-syntax

Existentialⁿ : Variadic-binding¹
Existentialⁿ = Quantⁿ Σ-syntax


Variadic² : Typeω
Variadic² =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ } ⦃ u : Underlying U ⦄
    {ℓ′ : Level} {V : Type ℓ′} ⦃ v : Underlying V ⦄
  → SCorr _ As U → SCorr _ As V
  → Corr  _ As (u .ℓ-underlying ⊔ v .ℓ-underlying)

Lift-op²⃑ⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ  : Level} {U : Type ℓ } ⦃ u : Underlying U ⦄
    {ℓ′ : Level} {V : Type ℓ′} ⦃ v : Underlying V ⦄
  → (∀ {ℓᵃ ℓᵇ } → Type ℓᵃ → Type ℓᵇ → Type (ℓᵃ ⊔ ℓᵇ))
  → SCorr _ As U → SCorr _ As V
  → Corr  _ As (u .ℓ-underlying ⊔ v .ℓ-underlying)
Lift-op²⃑ⁿ {0}           f P Q = f ⌞ P ⌟⁰ ⌞ Q ⌟⁰
Lift-op²⃑ⁿ {1}           f P Q = λ x → f ⌞ P x ⌟⁰ ⌞ Q x ⌟⁰
Lift-op²⃑ⁿ {suc (suc _)} f P Q = λ x → Lift-op²⃑ⁿ f (P x) (Q x)

Implⁿ : Variadic²
Implⁿ = Lift-op²⃑ⁿ λ A B → (A → B)

Prodⁿ : Variadic²
Prodⁿ = Lift-op²⃑ⁿ _×_

Sumⁿ : Variadic²
Sumⁿ = Lift-op²⃑ⁿ _⊎_


-- returns arity and codomain type
get-arity+type : ℕ → Type′ → Term × Type′
get-arity+type ninv = go 0 where
  clean-var  : ℕ → Term → Term
  clean-vars : ℕ → List (Arg Term) → List (Arg Term)

  -- variable references would be invalid in current context
  clean-var nbind (var v args) =
    if v <ᵇ nbind
       then var v (clean-vars nbind args)
       else var (v ∸ nbind) (clean-vars nbind args)
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
    first (plus-term ar) $ go nbind R
  go nbind (pi (varg t) (abs _ x)) = first suc-term $ go (suc nbind) x
  go nbind (pi _ (abs _ x)) = go (suc nbind) x
  go nbind (agda-sort (lit l)) = lit (nat 0) , agda-sort (lit l)
  go nbind (agda-sort (set r)) = lit (nat 0) , agda-sort (set (clean-var nbind r))
  go nbind x                   = lit (nat 0) , clean-var nbind x

-- returns inferred arity and codomain type
variadic-worker : Term → TC (Term × Term)
variadic-worker t = do
  ty ← (infer-type t >>= reduce) >>= wait-just-a-bit
  debug-print "tactic.variadic" 20 [ "Given type: " , term-err ty ]
  let ty , invs = strip-invisible ty
      ninv = length invs
  ctx-len ← length <$> get-context
  debug-print "tactic.variadic" 20 [ "Ctx len: " , term-err (lit (nat ctx-len)) ]
  let θ = drop (ctx-len ∸ ninv) $ count-from-to 0 ctx-len
  debug-print "tactic.variadic" 20 [ "Stripped type: " , term-err ty ]
  ty ← renameTC θ ty
  let ar , r = get-arity+type ninv ty
  debug-print "tactic.variadic" 20
    [ "Invisible args prefix length: " , term-err (lit (nat ninv)) , "\n"
    , "Stripped+substituted type: " , term-err ty , "\n"
    , "Inferred arity: " , term-err ar , "\n"
    , "Codomain: " , term-err r ]
  unify ty $ def (quote Arrows)
    [ varg ar , harg unknown , harg unknown , varg unknown , varg unknown ]
  pure $ ar , r

-- returns underlying instance
variadic-instance-worker : Term → TC Term
variadic-instance-worker r = do
  solved@(meta mv _) ← new-meta (def (quote Underlying) [ harg unknown , varg r ])
    where _ → type-error [ "Could not get `Underlying` instances: " , term-err r ]
  (und ∷ []) ← get-instances mv where
    [] → type-error [ "No `Underlying `instances for ", term-err r ]
    _  → type-error [ "Multiple `Underlying` instances for ", term-err r ]
  unify solved und
  pure und


unop-macro : Name → Term → Term → TC ⊤
unop-macro nam t hole = do
  ar , r ← variadic-worker t
  und ← variadic-instance-worker r
  unify hole $ def nam
    [ harg ar , harg unknown , harg unknown
    , harg unknown , harg unknown , iarg und
    , varg t ]

infixr 0 ¬̇_
macro
  ⌞_⌟ = unop-macro (quote Carrierⁿ)
  ¬̇_  = unop-macro (quote Negⁿ)


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
infixr 8  _×̇_
infixr 7  _⊎̇_
macro
  _→̇_ = binop-macro (quote Implⁿ)
  _×̇_ = binop-macro (quote Prodⁿ)
  _⊎̇_ = binop-macro (quote Sumⁿ)
