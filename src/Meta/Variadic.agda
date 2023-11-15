{-# OPTIONS --safe #-}
-- -vtactic.variadic:20
module Meta.Variadic where

open import Foundations.Base

open import Meta.Reflection

open import Correspondences.Base

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct

private variable
  ℓᵃ ℓ : Level

-- returns reflected arity, tuple of argument types, level and result type
get-arity-sig-lvl-type : Type′ → Term × Type′ × Type′ × Type′
get-arity-sig-lvl-type t =
  let ar , sig , lv , R = go t
  in ar , list→tuple sig , lv , R where
    fold-r′ : (Term → Term → Term) → Term → List Term → Term
    fold-r′ _ x [] = x
    fold-r′ f x (a ∷ []) = a
    fold-r′ f x (a₁ ∷ a₂ ∷ as) = f a₁ (fold-r′ f x (a₂ ∷ as))

    list→tuple = fold-r′ (λ x y → con (quote _,_) [ varg x , varg y ]) unknown

    clean-var : Term → Term
    clean-vars : List (Arg Term) → List (Arg Term)

    -- variable references would be invalid in current context
    -- so have to kill them and rely on unification
    clean-var (var _ _) = unknown
    clean-var (con c args) = con c (clean-vars args)
    clean-var (def f args) = def f (clean-vars args)
    clean-var (lam v (abs s x)) = lam v (abs s (clean-var x))
    clean-var (pi (arg v a) (abs s b)) = pi (arg v (clean-var a)) (abs s (clean-var b))
    clean-var x = x

    clean-vars [] = []
    clean-vars (arg ai x ∷ xs) = arg ai (clean-var x) ∷ clean-vars xs

    go : Term → Term × List Type′ × Type′ × Type′
    go (def (quote Arrows) (ar v∷ l h∷ ls h∷ sig v∷ R v∷ [])) = ar , [ sig ] , l , R
    go (pi (varg t) (abs _ x)) =
      let ar , sig , lv , R = go x
      in suc-term ar , clean-var t ∷ sig , lv , R
    go (pi _        (abs _ x)) = go x
    go (agda-sort (lit l)) = lit (nat 0) , [] , lit (nat l) , agda-sort (lit l)
    go x                   = lit (nat 0) , [] , unknown , clean-var x

quantifier-macro : Name → Term → Term → TC ⊤
quantifier-macro nam t hole = withReduceDefs (false , [ quote Arrows ]) do
  ty ← inferType t >>= reduce
  debugPrint "tactic.variadic" 20 ["Type hint: " , termErr ty ]
  let ar , sig , lv , r = get-arity-sig-lvl-type ty
  unify hole $ def nam $
    [ harg ar , harg lv
    , harg unknown , harg sig , varg t ]

impl-macro : Term → Term → Term → TC ⊤
impl-macro p q hole = withReduceDefs (false , [ quote Arrows ]) do
  pty ← inferType p >>= reduce
  let par , psig , plv , pr = get-arity-sig-lvl-type pty
  unify hole $ def (quote Implⁿ)
    [ harg par , harg plv , harg unknown
    , harg unknown , harg psig , varg p , varg q ]

macro
  Π[_] = quantifier-macro (quote Universalⁿ)
  ∀[_] = quantifier-macro (quote IUniversalⁿ)
  Σ[_] = quantifier-macro (quote Existentialⁿ)
  _⇒_  = impl-macro

-- bleb : {A : Type ℓᵃ} (P : n-Corr _ 2 ℓ (A , A , A)) → Corr³ ℓ (A , A , A)
-- bleb {A} P = ⌞ P ⌟ⁿ

-- module bek
--   {A : Type ℓᵃ} {B : Type ℓ}
--   {P : n-Corr 3 2 ℓ (A , B , A)}
--   {Q : Corr 3 ℓ (A , B , A)}
--   where

--   test₂ : Corr³ ℓ _
--   test₂ = ⌞ P ⌟ⁿ

--   lel : Π[ ⌞ P ⌟ⁿ ]
--   lel x y z = {!!}

--   open import Truncation.Propositional.Base
--   kek : ∃[ ⌞ P ⌟ⁿ ⇒ Q ]
--   kek = ∣ {!!} , {!!} , {!!} , {!!} ∣₁
