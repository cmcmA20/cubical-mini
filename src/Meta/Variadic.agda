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

get-arity-sig-type : Type′ → Term × Type′
get-arity-sig-type = second (fold-r′ (λ x y → con (quote _,_) [ varg x , varg y ]) unknown) ∘ go where
  fold-r′ : (Term → Term → Term) → Term → List Term → Term
  fold-r′ _ x [] = x
  fold-r′ f x (a ∷ []) = a
  fold-r′ f x (a₁ ∷ a₂ ∷ as) = f a₁ (fold-r′ f x (a₂ ∷ as))

  sig-go : Term → Term
  sig-gos : List (Arg Term) → List (Arg Term)

  -- variable references would be invalid in current context
  -- so have to kill them and rely on unification
  sig-go (var _ _) = unknown
  sig-go (con c args) = con c (sig-gos args)
  sig-go (def f args) = def f (sig-gos args)
  sig-go (lam v (abs s x)) = lam v (abs s (sig-go x))
  sig-go (pi (arg v a) (abs s b)) = pi (arg v (sig-go a)) (abs s (sig-go b))
  sig-go x = x

  sig-gos [] = []
  sig-gos (arg ai x ∷ xs) = arg ai (sig-go x) ∷ sig-gos xs

  go : Term → Term × List Type′
  go (def (quote Arrows) (ar v∷ l h∷ ls h∷ sig v∷ R v∷ [])) = ar , [ sig ]
  go (pi (varg t) (abs _ x)) = bimap suc-term (sig-go t ∷_) $ go x
  go (pi _        (abs _ x)) = go x
  go _                       = lit (nat 0) , []

carrier-macro : Term → Term → TC ⊤
carrier-macro t hole = withReduceDefs (false , [ quote Arrows ]) do
  ty ← inferType t >>= reduce
  let ar , sig = get-arity-sig-type ty
  unify hole $ def (quote Carrierⁿ)
    [ harg unknown , harg ar
    , harg unknown , harg unknown
    , harg sig , varg t ]

quantifier-macro : Name → Term → Term → TC ⊤
quantifier-macro nam t hole = withReduceDefs (false , [ quote Arrows ]) do
  ty ← inferType t >>= reduce
  debugPrint "tactic.variadic" 20 ["Type hint: " , termErr ty ]
  let ar , sig = get-arity-sig-type ty
  unify hole $ def nam $
    [ harg ar , harg unknown
    , harg unknown , harg sig , varg t ]

impl-macro : Term → Term → Term → TC ⊤
impl-macro p q hole = withReduceDefs (false , [ quote Arrows ]) do
  pty ← inferType p >>= reduce
  let par , psig = get-arity-sig-type pty
  unify hole $ def (quote Implⁿ)
    [ harg par , harg unknown , harg unknown
    , harg unknown , harg psig , varg p , varg q ]

macro
  ⌞_⌟ⁿ = carrier-macro
  Π[_] = quantifier-macro (quote Universalⁿ)
  ∀[_] = quantifier-macro (quote IUniversalⁿ)
  Σ[_] = quantifier-macro (quote Existentialⁿ)
  ∃[_] = quantifier-macro (quote Existential₁ⁿ)
  _⇒_ = impl-macro

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
