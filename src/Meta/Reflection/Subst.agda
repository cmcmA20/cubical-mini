{-# OPTIONS --safe --no-exact-split #-}
module Meta.Reflection.Subst where

open import Foundations.Base

open import Meta.Effect.Bind
open import Meta.Effect.Foldable
open import Meta.Effect.Idiom
open import Meta.Effect.Map
open import Meta.Effect.Traversable
open import Meta.Reflection.Base

open import Data.Bool.Base
open import Data.List.Base as List
open import Data.List.Operations
open import Data.List.Instances.Bind
open import Data.List.Instances.Foldable
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Map
open import Data.List.Instances.Traversable
open import Data.Maybe.Base
open import Data.Maybe.Instances.Bind
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

data Subst : Type where
  idₛ        : Subst
  _∷ₛ_       : Term → Subst → Subst
  wk         : ℕ → Subst → Subst
  lift       : ℕ → Subst → Subst
  strengthen : ℕ → Subst → Subst

infixr 20 _∷ₛ_

wkS : ℕ → Subst → Subst
wkS 0 ρ        = ρ
wkS n (wk x ρ) = wk (n + x) ρ
wkS n ρ        = wk n ρ

liftS : ℕ → Subst → Subst
liftS 0 ρ          = ρ
liftS n idₛ        = idₛ
liftS n (lift k ρ) = lift (n + k) ρ
liftS n ρ          = lift n ρ

_++#_ : List Term → Subst → Subst
x ++# ρ = fold-r (_∷ₛ_) ρ x
infix 15 _++#_

raiseS : ℕ → Subst
raiseS n = wk n idₛ

raise-fromS : ℕ → ℕ → Subst
raise-fromS n k = liftS n $ raiseS k

--            Γ, Δ ⊢ u : A
-- ---------------------------------
-- Γ, Δ ⊢ singletonS |Δ| u : Γ, A, Δ
singletonS : ℕ → Term → Subst
singletonS n u = ((λ m → var m []) <$> count-from-to 0 n) ++# u ∷ₛ raiseS n

--           Γ, A, Δ ⊢ u : A
-- ----------------------------------
-- Γ, A, Δ ⊢ inplaceS |Δ| u : Γ, A, Δ
inplaceS : ℕ → Term → Subst
inplaceS n u = ((λ m → var m []) <$> count-from-to 0 n) ++# u ∷ₛ raiseS (suc n)


private variable
  ℓ : Level
  A : Type ℓ

-- using wf in reflection is an overkill innit
record Has-subst {ℓ} (A : Type ℓ) : Type (ℓsuc ℓ) where
  field applyS : Subst → A → Maybe A

open Has-subst ⦃ ... ⦄ using (applyS) public

raise : ⦃ _ : Has-subst A ⦄ → ℕ → A → Maybe A
raise n = applyS (raiseS n)

raise* : ⦃ _ : Has-subst A ⦄ → ℕ → List A → Maybe (List A)
raise* n = traverse (raise n)

applyS* : ⦃ _ : Has-subst A ⦄ → Subst → List A → Maybe (List A)
applyS* ρ = traverse (applyS ρ)

instance
  Has-subst-Arg : ⦃ _ : Has-subst A ⦄ → Has-subst (Arg A)
  Has-subst-Arg .applyS ρ (arg ai x) = arg ai <$> applyS ρ x


-- fueled
subst-clause : ℕ → Subst → Clause → Maybe Clause
subst-tm     : ℕ → Subst → Term → Maybe Term
subst-tm*    : ℕ → Subst → List (Arg Term) → Maybe (List (Arg Term))
apply-tm     : ℕ → Term → Arg Term → Maybe Term
subst-tel    : ℕ → Subst → Telescope → Maybe Telescope

instance
  Has-subst-Term : Has-subst Term
  Has-subst-Term = record { applyS = with-full-tank subst-tm }

  Has-subst-Clause : Has-subst Clause
  Has-subst-Clause = record { applyS = with-full-tank subst-clause }

  Has-subst-Args : Has-subst (List (Arg Term))
  Has-subst-Args = record { applyS = with-full-tank subst-tm* }

  Has-subst-Telescope : Has-subst Telescope
  Has-subst-Telescope = record { applyS = with-full-tank subst-tel }

subst-tm* 0          _ _              = nothing
subst-tm* (suc fuel) ρ []             = pure []
subst-tm* (suc fuel) ρ (arg ι x ∷ ls) = do
  x′  ← subst-tm fuel ρ x
  ls′ ← subst-tm* fuel ρ ls
  pure $ arg ι x′ ∷ ls′

apply-tm* : ℕ → Term → List (Arg Term) → Maybe Term
apply-tm* 0          _  _        = nothing
apply-tm* (suc fuel) tm []       = pure tm
apply-tm* (suc fuel) tm (x ∷ xs) = do
  t ← apply-tm fuel tm x
  apply-tm* fuel t xs

lookup-tm : ℕ → (σ : Subst) (i : ℕ) → Maybe Term
lookup-tm 0 _ _ = nothing
lookup-tm (suc fuel) idₛ i = pure $ var i []
lookup-tm (suc fuel) (wk n idₛ) i = pure $ var (i + n) []
lookup-tm (suc fuel) (wk n ρ) i = do
  t ← lookup-tm fuel ρ i
  subst-tm fuel (raiseS n) t
lookup-tm (suc fuel) (x ∷ₛ ρ) i with (i == 0)
… | true  = pure x
… | false = lookup-tm fuel ρ (i ∸ 1)
lookup-tm (suc fuel) (strengthen n ρ) i with (i <? n)
… | true  = pure unknown
… | false = lookup-tm fuel ρ (i ∸ n)
lookup-tm (suc fuel) (lift n σ) i with (i <? n)
… | true  = pure $ var i []
… | false = do
  t ← lookup-tm fuel σ (i ∸ n)
  subst-tm fuel (raiseS n) t

apply-tm 0 _ _ = nothing
apply-tm (suc fuel) (var x args)      argu = pure $ var x (args ++ argu ∷ [])
apply-tm (suc fuel) (con c args)      argu = pure $ con c (args ++ argu ∷ [])
apply-tm (suc fuel) (def f args)      argu = pure $ def f (args ++ argu ∷ [])
apply-tm (suc fuel) (lam v (abs n t)) (arg _ argu) = subst-tm fuel (argu ∷ₛ idₛ) t
apply-tm (suc fuel) (pat-lam cs args) argu = pure $ pat-lam cs (args ++ argu ∷ [])
apply-tm (suc fuel) (pi a b)          argu = pure $ pi a b
apply-tm (suc fuel) (agda-sort s)     argu = pure $ agda-sort s
apply-tm (suc fuel) (lit l)           argu = pure $ lit l
apply-tm (suc fuel) (meta x args)     argu = pure $ meta x (args ++ argu ∷ [])
apply-tm (suc fuel) unknown           argu = pure unknown

subst-tm 0 _ _ = nothing
subst-tm (suc fuel) idₛ tm = pure tm
subst-tm (suc fuel) ρ (var i args)      = do
  a ← lookup-tm fuel ρ i
  b ← subst-tm* fuel ρ args
  apply-tm* fuel a b
subst-tm (suc fuel) ρ (con c args)      = con c <$> subst-tm* fuel ρ args
subst-tm (suc fuel) ρ (def f args)      = def f <$> subst-tm* fuel ρ args
subst-tm (suc fuel) ρ (meta x args)     = meta x <$> subst-tm* fuel ρ args
subst-tm (suc fuel) ρ (pat-lam cs args) = do
  a ← traverse (subst-clause fuel ρ) cs
  b ← subst-tm* fuel ρ args
  pure $ pat-lam a b
subst-tm (suc fuel) ρ (lam v (abs n b)) =
  lam v ∘ abs n <$> subst-tm fuel (liftS 1 ρ) b
subst-tm (suc fuel) ρ (pi (arg ι a) (abs n b)) = do
  a′ ← subst-tm fuel ρ a
  b′ ← subst-tm fuel (liftS 1 ρ) b
  pure $ pi (arg ι a′) (abs n b′)
subst-tm (suc fuel) ρ (lit l) = pure $ lit l
subst-tm (suc fuel) ρ unknown = pure unknown
subst-tm (suc fuel) ρ (agda-sort s) with s
… | set t      = agda-sort ∘ set <$> subst-tm fuel ρ t
… | lit n      = pure $ agda-sort (lit n)
… | prop t     = agda-sort ∘ prop <$> subst-tm fuel ρ t
… | prop-lit n = pure $ agda-sort (prop-lit n)
… | inf n      = pure $ agda-sort (inf n)
… | unknown    = pure unknown

subst-tel 0 _ _ = nothing
subst-tel (suc fuel) ρ []                    = pure []
subst-tel (suc fuel) ρ ((x , arg ai t) ∷ xs) = do
  x′  ← subst-tm fuel ρ t
  xs′ ← subst-tel fuel (liftS 1 ρ) xs
  pure $ (x , arg ai x′) ∷ xs′

subst-clause 0 _ _ = nothing
subst-clause (suc fuel) σ (clause tel ps t)      = do
  a ← subst-tel fuel σ tel
  b ← subst-tm fuel (liftS (length tel) σ) t -- TODO need tests for this
  pure $ clause a ps b
subst-clause (suc fuel) σ (absurd-clause tel ps) = do
  x ← subst-tel fuel σ tel
  pure $ absurd-clause x ps

_<#>_ : Maybe Term → Arg Term → Maybe Term
f <#> x = do
  f ← f
  with-full-tank apply-tm f x

infixl 7 _<#>_

pi-apply : Term → List (Arg Term) → Maybe Term
pi-apply ty as = go ty as idₛ where
  go : Term → List (Arg Term) → Subst → Maybe Term
  go (pi (arg _ x) (abs n y)) (arg _ a ∷ as) s = go y as (a ∷ₛ s)
  go _ (_ ∷ as) s = nothing
  go t [] s = applyS s t

maybe→tc : Maybe A →  (err : List ErrorPart) → TC A
maybe→tc act err with act
... | just x = pure x
... | nothing = type-error err

pi-applyTC : Term → List (Arg Term) → TC Term
pi-applyTC t as = maybe→tc (pi-apply t as)
                           ([ "Failed to apply type " , term-err t ])

raiseTC : ⦃ _ : Has-subst A ⦄ → ℕ → A → TC A
raiseTC n a = maybe→tc (raise n a) [ "Failed to raise term " ]

substTC : ⦃ _ : Has-subst A ⦄ → Subst → A → TC A
substTC θ a = maybe→tc (applyS θ a) [ "Failed to substitute in term " ]

applyS*TC : ⦃ _ : Has-subst A ⦄ → Subst → List A → TC (List A)
applyS*TC ρ xs = maybe→tc (applyS* ρ xs) [ "Failed to apply in terms " ]

applyTC : Term → Arg Term → TC Term
applyTC f x = maybe→tc (with-full-tank apply-tm f x) [ "Failed to apply function " , term-err f ]

apply*TC : Term → Args → TC Term
apply*TC f x = maybe→tc (with-full-tank apply-tm* f x) [ "Failed to apply function " , term-err f ]


-- very unsafe way to do this
-- you should enforce that all the elements are unique
Ren : Type
Ren = List ℕ

-- TODO refactor
inverseR : Ren → Ren
inverseR = go 0 ∘ insertion-sort (λ x y → x .fst <? suc (y .fst)) ∘ (λ vs → zip vs (count-from-to 0 (length vs))) where
  go : ℕ → List (ℕ × ℕ) → Ren
  go n [] = []
  go n ((k , v) ∷ ss) = count-from-to n k ++ (v ∷ go (suc k) ss)

ren→sub : Ren → Subst
ren→sub vs = ((λ v → var v []) <$> vs) ++# idₛ

rename-tm : (fuel : ℕ) → Ren → Term → Maybe Term
rename-tm fuel = subst-tm fuel ∘ ren→sub

renameTC : ⦃ _ : Has-subst A ⦄ → Ren → A → TC A
renameTC vs tm = maybe→tc (applyS (ren→sub vs) tm) [ "Failed to rename term " ]

generalize : List ℕ → Term → TC Term
generalize fvs t
  =   iter (length fvs) (pi (varg unknown) ∘ abs "x")
  <$> renameTC (inverseR fvs) t
