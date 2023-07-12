{-# OPTIONS --safe #-}
module Meta.Subst where

open import Foundations.Base

open import Meta.Bind
open import Meta.Reflection

open import Data.Bool.Base
open import Data.List.Base as List
open import Data.List.Instances.Bind
open import Data.Maybe.Base
open import Data.Maybe.Instances.Bind
open import Data.Nat.Base
open import Data.Nat.Order

data Subst : Type where
  idₛ        : Subst
  _∷ₛ_       : Term → Subst → Subst
  wk         : ℕ → Subst → Subst
  lift       : ℕ → Subst → Subst
  strengthen : ℕ → Subst → Subst

infixr 20 _∷ₛ_

wkS : ℕ → Subst → Subst
wkS 0 ρ = ρ
wkS n (wk x ρ) = wk (n + x) ρ
wkS n ρ        = wk n ρ

liftS : ℕ → Subst → Subst
liftS 0 ρ       = ρ
liftS n idₛ        = idₛ
liftS n (lift k ρ) = lift (n + k) ρ
liftS n ρ          = lift n ρ

_++#_ : List Term → Subst → Subst
x ++# ρ = List.fold-r (_∷ₛ_) ρ x
infix 15 _++#_

raiseS : ℕ → Subst
raiseS n = wk n idₛ

raise-fromS : ℕ → ℕ → Subst
raise-fromS n k = liftS n $ raiseS k

singletonS : ℕ → Term → Subst
singletonS n u = ((λ m → var m []) <$> count (n - 1)) ++# u ∷ₛ raiseS n where
  count : ℕ → List ℕ
  count zero = []
  count (suc n) = 0 ∷ (suc <$> count n)


subst-tm  : (fuel : ℕ) → Subst → Term → Maybe Term
subst-tm* : (fuel : ℕ) → Subst → List (Arg Term) → Maybe (List (Arg Term))
apply-tm  : (fuel : ℕ) → Term → Arg Term → Maybe Term

raise : (fuel : ℕ) → ℕ → Term → Maybe Term
raise fuel n = subst-tm fuel (raiseS n)

subst-tm* 0 _ _ = nothing
subst-tm* (suc fuel) ρ [] = pure []
subst-tm* (suc fuel) ρ (arg ι x ∷ ls) = do
  x ← subst-tm fuel ρ x
  (arg ι x ∷_) <$> subst-tm* fuel ρ ls

apply-tm* : (fuel : ℕ) → Term → List (Arg Term) → Maybe Term
apply-tm* 0 _ _ = nothing
apply-tm* (suc fuel) tm [] = pure tm
apply-tm* (suc fuel) tm (x ∷ xs) = do
  tm′ ← apply-tm fuel tm x
  apply-tm* fuel tm′ xs

lookup-tm : (fuel : ℕ) (σ : Subst) (i : ℕ) → Maybe Term
lookup-tm 0 _ _ = nothing
lookup-tm (suc fuel) idₛ i = pure $ var i []
lookup-tm (suc fuel) (wk n idₛ) i = pure $ var (i + n) []
lookup-tm (suc fuel) (wk n ρ) i = lookup-tm fuel ρ i >>= subst-tm fuel (raiseS n)
lookup-tm (suc fuel) (x ∷ₛ ρ) i with (i == 0)
… | true  = pure x
… | false = lookup-tm fuel ρ (i - 1)
lookup-tm (suc fuel) (strengthen n ρ) i with (i <-internal n)
… | true = nothing
… | false = lookup-tm fuel ρ (i - n)
lookup-tm (suc fuel) (lift n σ) i with (i <-internal n)
… | true  = pure $ var i []
… | false = lookup-tm fuel σ (i - n) >>= raise fuel n

apply-tm 0 _ _ = nothing
apply-tm (suc fuel) (var x args)      argu = pure $ var x (args ++ argu ∷ [])
apply-tm (suc fuel) (con c args)      argu = pure $ con c (args ++ argu ∷ [])
apply-tm (suc fuel) (def f args)      argu = pure $ def f (args ++ argu ∷ [])
apply-tm (suc fuel) (lam v (abs n t)) (arg _ argu) = subst-tm fuel (argu ∷ₛ idₛ) t
apply-tm (suc fuel) (pat-lam cs args) argu = nothing
apply-tm (suc fuel) (pi a b)          argu = nothing
apply-tm (suc fuel) (agda-sort s)     argu = nothing
apply-tm (suc fuel) (lit l)           argu = nothing
apply-tm (suc fuel) (meta x args)     argu = pure $ meta x (args ++ argu ∷ [])
apply-tm (suc fuel) unknown           argu = pure unknown

subst-tm 0 _ _ = nothing
subst-tm (suc fuel) idₛ tm = pure tm
subst-tm (suc fuel) ρ (var i args) = do
  r ← lookup-tm fuel ρ i
  es ← subst-tm* fuel ρ args
  apply-tm* fuel r es
subst-tm (suc fuel) ρ (con c args)      = con c <$> subst-tm* fuel ρ args
subst-tm (suc fuel) ρ (def f args)      = def f <$> subst-tm* fuel ρ args
subst-tm (suc fuel) ρ (meta x args)     = meta x <$> subst-tm* fuel ρ args
subst-tm (suc fuel) ρ (pat-lam cs args) = nothing
subst-tm (suc fuel) ρ (lam v (abs n b)) = lam v ∘ abs n <$> subst-tm fuel (liftS 1 ρ) b
subst-tm (suc fuel) ρ (pi (arg ι a) (abs n b)) = do
  a ← subst-tm fuel ρ a
  b ← subst-tm fuel (liftS 1 ρ) b
  pure (pi (arg ι a) (abs n b))
subst-tm (suc fuel) ρ (lit l) = pure (lit l)
subst-tm (suc fuel) ρ unknown = pure unknown
subst-tm (suc fuel) ρ (agda-sort s) with s
… | set t     = agda-sort ∘ set <$> subst-tm fuel ρ t
… | lit n     = pure (agda-sort (lit n))
… | prop t    = agda-sort ∘ prop <$> subst-tm fuel ρ t
… | propLit n = pure (agda-sort (propLit n))
… | inf n     = pure (agda-sort (inf n))
… | unknown   = pure unknown
