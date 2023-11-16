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
  : (arity : ℕ) {ls : Levels arity} (As : Types arity ls)
    {ℓ : Level} (U : Type ℓ) ⦃ u : Underlying U ⦄
  → Type (ℓ ⊔ ℓsup arity ls)
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
  : (arity : ℕ) {ls : Levels arity} (As : Types arity ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup arity ls)
Corr arity As ℓ = SCorr arity As (Type ℓ)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3
Corr⁴ = Corr 4
Corr⁵ = Corr 5

Pred = Corr¹


Carrierⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {P : Type ℓ} ⦃ u : Underlying P ⦄
  → SCorr arity As P → Corr arity As (u .ℓ-underlying)
Carrierⁿ {0}           C   = ⌞ C ⌟⁰
Carrierⁿ {1}           C a = ⌞ C a ⌟⁰
Carrierⁿ {suc (suc _)} C a = Carrierⁿ (C a)

Universalⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types arity ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr arity As U → Type (u .ℓ-underlying ⊔ ℓsup arity ls)
Universalⁿ {0}                         P = ⌞ P ⌟⁰
Universalⁿ {1}           {As = A}      P = Π[ a ꞉ A ] ⌞ P a ⌟⁰
Universalⁿ {suc (suc _)} {As = A , As} P = Π[ a ꞉ A ] Universalⁿ (P a)

IUniversalⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types arity ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr arity As U → Type (u .ℓ-underlying ⊔ ℓsup arity ls)
IUniversalⁿ {0}                         P = ⌞ P ⌟⁰
IUniversalⁿ {1}           {As = A}      P = ∀{a} → ⌞ P a ⌟⁰
IUniversalⁿ {suc (suc _)} {As = A , As} P = ∀{a} → IUniversalⁿ (P a)

Existentialⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types arity ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr arity As U → Type (u .ℓ-underlying ⊔ ℓsup arity ls)
Existentialⁿ {0}                         P = ⌞ P ⌟⁰
Existentialⁿ {1}           {As = A}      P = Σ[ a ꞉ A ] ⌞ P a ⌟⁰
Existentialⁿ {suc (suc _)} {As = A , As} P = Σ[ a ꞉ A ] Existentialⁿ (P a)


Implⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types arity ls}
    {ℓ  : Level} {U : Type ℓ } ⦃ u : Underlying U ⦄
    {ℓ′ : Level} {V : Type ℓ′} ⦃ v : Underlying V ⦄
  → SCorr arity As U → SCorr arity As V → Corr arity As (u .ℓ-underlying ⊔ v .ℓ-underlying)
Implⁿ {0}           P Q = ⌞ P ⌟⁰ → ⌞ Q ⌟⁰
Implⁿ {1}           P Q = λ x → ⌞ P x ⌟⁰ → ⌞ Q x ⌟⁰
Implⁿ {suc (suc _)} P Q = λ x → Implⁿ (P x) (Q x)

Prodⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types arity ls}
    {ℓ  : Level} {U : Type ℓ } ⦃ u : Underlying U ⦄
    {ℓ′ : Level} {V : Type ℓ′} ⦃ v : Underlying V ⦄
  → SCorr arity As U → SCorr arity As V → Corr arity As (u .ℓ-underlying ⊔ v .ℓ-underlying)
Prodⁿ {0}           P Q = ⌞ P ⌟⁰ × ⌞ Q ⌟⁰
Prodⁿ {1}           P Q = λ x → ⌞ P x ⌟⁰ × ⌞ Q x ⌟⁰
Prodⁿ {suc (suc _)} P Q = λ x → Prodⁿ (P x) (Q x)


-- batshit insane garbage, beware

-- returns reflected arity, tuple of argument types, level and result type
get-arity-sig-lvl-type : Type′ → Term × Type′ × Type′ × Type′
get-arity-sig-lvl-type t =
  let ar , sig , lv , R = go 0 t
  in ar , list→tuple sig , lv , R where
    fold-r′ : (Term → Term → Term) → Term → List Term → Term
    fold-r′ _ x [] = x
    fold-r′ f x (a ∷ []) = a
    fold-r′ f x (a₁ ∷ a₂ ∷ as) = f a₁ (fold-r′ f x (a₂ ∷ as))

    list→tuple = fold-r′ (λ x y → con (quote _,_) [ varg x , varg y ]) unknown

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
    clean-var nbind (pi (arg v a) (abs s b)) = pi (arg v (clean-var nbind a)) (abs s (clean-var (suc nbind) b))
    clean-var nbind x = x

    clean-vars nbind [] = []
    clean-vars nbind (arg ai x ∷ xs) = arg ai (clean-var nbind x) ∷ clean-vars nbind xs

    go : ℕ → Term → Term × List Type′ × Type′ × Type′
    go nbind (def (quote Arrows) (ar v∷ l h∷ ls h∷ sig v∷ R v∷ [])) = ar , [ sig ] , l , R
    go nbind (pi (varg t) (abs _ x)) =
      let ar , sig , lv , R = go (suc nbind) x
      in suc-term ar , clean-var nbind t ∷ sig , lv , R
    go nbind (pi _        (abs _ x)) = go (suc nbind) x
    go nbind (agda-sort (lit l)) = lit (nat 0) , [] , lit (nat l) , agda-sort (lit l)
    go nbind x                   = lit (nat 0) , [] , unknown , clean-var nbind x

carrier-macro : Term → Term → TC ⊤
carrier-macro t hole = withReduceDefs (false , [ quote Arrows ]) do
  ty ← inferType t >>= reduce
  debugPrint "tactic.variadic" 20 [ "Type hint: " , termErr ty ]
  let ar , sig , lv , r = get-arity-sig-lvl-type ty
  solved@(meta mv _) ← new-meta (def (quote Underlying) [ harg unknown , varg r ])
    where _ → typeError [ "Could not get `Underlying` instances: " , termErr r ]
  (und ∷ []) ← getInstances mv where
    [] → typeError [ "No `Underlying `instances for ", termErr r ]
    _  → typeError [ "Multiple `Underlying` instances for ", termErr r ]
  unify solved und
  let
    solution = def (quote Carrierⁿ)
      [ harg ar , harg unknown , harg sig
      , harg lv , harg r , iarg und
      , varg t ]
  debugPrint "tactic.variadic" 20
    [ "Candidate solution: " , termErr solution , "\n"
    , "Arity: " , termErr ar , "\n"
    , "Signature: " , termErr sig , "\n"
    , "Level: " , termErr lv , "\n" ]
  unify hole solution

macro ⌞_⌟ = carrier-macro

quantifier-macro : Name → Term → Term → TC ⊤
quantifier-macro nam t hole = withReduceDefs (false , [ quote Arrows ]) do
  ty ← (inferType t >>= reduce) >>= wait-just-a-bit
  debugPrint "tactic.variadic" 20 ["Type hint: " , termErr ty ]
  let ar , sig , lv , r = get-arity-sig-lvl-type ty
  solved@(meta mv _) ← new-meta (def (quote Underlying) [ harg unknown , varg r ])
    where _ → typeError [ "Could not get `Underlying` instances: " , termErr r ]
  (und ∷ []) ← getInstances mv where
    [] → typeError [ "No `Underlying `instances for ", termErr r ]
    _  → typeError [ "Multiple `Underlying` instances for ", termErr r ]
  unify solved und
  unify hole $ def nam $
    [ harg ar , harg unknown , harg sig
    , harg lv , harg r , iarg und
    , varg t ]

macro
  Π[_] = quantifier-macro (quote Universalⁿ)
  ∀[_] = quantifier-macro (quote IUniversalⁿ)
  Σ[_] = quantifier-macro (quote Existentialⁿ)


binop-macro : Name → Term → Term → Term → TC ⊤
binop-macro nam p q hole = withReduceDefs (false , [ quote Arrows ]) do
  pty ← (inferType p >>= reduce) >>= wait-just-a-bit
  debugPrint "tactic.variadic" 20 ["P type hint: " , termErr pty ]
  qty ← (inferType q >>= reduce) >>= wait-just-a-bit
  debugPrint "tactic.variadic" 20 ["Q type hint: " , termErr qty ]
  let par , psig , plv , pr = get-arity-sig-lvl-type pty
  let qar , qsig , qlv , qr = get-arity-sig-lvl-type qty
  unify par qar
  psolved@(meta pmv _) ← new-meta (def (quote Underlying) [ harg plv , varg pr ])
    where _ → typeError [ "Could not get `Underlying` instances: " , termErr pr ]
  (pund ∷ []) ← getInstances pmv where
    [] → typeError [ "No `Underlying `instances for ", termErr pr ]
    _  → typeError [ "Multiple `Underlying` instances for ", termErr pr ]
  unify psolved pund
  qsolved@(meta qmv _) ← new-meta (def (quote Underlying) [ harg qlv , varg qr ])
    where _ → typeError [ "Could not get `Underlying` instances: " , termErr qr ]
  (qund ∷ []) ← getInstances qmv where
    [] → typeError [ "No `Underlying `instances for ", termErr qr ]
    _  → typeError [ "Multiple `Underlying` instances for ", termErr qr ]
  unify qsolved qund
  unify-loudly hole $ def nam
    [ harg par , harg unknown , harg psig
    , harg plv , harg pr , iarg pund
    , harg qlv , harg qr , iarg qund
    , varg p , varg q ]

macro
  _⇒_  = binop-macro (quote Implⁿ)
  _××_  = binop-macro (quote Prodⁿ)
