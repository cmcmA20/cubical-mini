{-# OPTIONS --safe --no-exact-split #-}
module Meta.Reflection.Base where

open import Foundations.Prelude
  renaming ( _∘_ to _∘ₜ_
           )

open import Meta.Literals.FromNat     public
open import Meta.Literals.FromString  public
open import Meta.Literals.FromProduct public

open import Meta.Effect.Map
open import Meta.Effect.Idiom
open import Meta.Effect.Bind public
open import Meta.Effect.Alt
open import Meta.Effect.Traversable
open import Meta.Reflection.Argument
open import Meta.Reflection.Neutral

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.List.Base as List
open import Data.List.Instances.Append
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom
open import Data.List.Instances.Traversable
open import Data.List.Operations as List
open import Data.Maybe.Base
open import Data.Maybe.Instances.Idiom
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
open import Data.String.Base

open import Agda.Builtin.Reflection public
  using ( TC ; bindTC ; returnTC ; catchTC ; commitTC
        ; blockTC ; quoteTC ; unquoteTC ; quoteωTC
        ; reduce ; normalise ; unify )
  renaming ( inferType to infer-type
           ; checkType to check-type
           ; extendContext to extend-context
           ; inContext to in-context
           ; freshName to fresh-name
           ; declareDef to declare-def
           ; declareData to declare-data
           ; defineData to define-data
           ; declarePostulate to declare-postulate
           ; defineFun to define-function
           ; getType to get-type
           ; getDefinition to get-definition
           ; getContext to get-context
           ; isMacro to is-macro?
           ; typeError to type-error
           ; formatErrorParts to format-error-parts
           ; debugPrint to debug-print
           ; withNormalisation to with-normalisation
           ; askNormalisation to ask-normalisation
           ; withReconstructed to with-reconstructed
           ; askReconstructed to ask-reconstructed
           ; withExpandLast to with-expand-last
           ; askExpandLast to ask-expand-last
           ; withReduceDefs to with-reduce-defs
           ; askReduceDefs to ask-reduce-defs
           ; noConstraints to no-constraints
           ; runSpeculative to run-speculative
           ; getInstances to get-instances
           ; blockOnMeta to block-on-meta
           )

instance
  Map-TC : Map (eff TC)
  Map-TC .map f x = bindTC x λ x → returnTC (f x)

  Idiom-TC : Idiom (eff TC)
  Idiom-TC .pure = returnTC
  Idiom-TC ._<*>_ f g = bindTC f λ f → bindTC g λ g → pure (f g)

  Bind-TC : Bind (eff TC)
  Bind-TC ._>>=_ = bindTC

  Alt-TC : Alt (eff TC)
  Alt-TC .fail  = type-error []
  Alt-TC ._<|>_ = catchTC

  Map-Arg : Map (eff Arg)
  Map-Arg .map f (arg ai x) = arg ai (f x)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : ℕ

full-tank : ℕ
full-tank = 1234567890

with-full-tank : (ℕ → A) → A
with-full-tank f = f full-tank

under-abs : Term → TC A → TC A
under-abs (lam v (abs nm _)) m = extend-context nm (arg (arg-info v (modality relevant quantity-ω)) unknown) m
under-abs (pi a (abs nm _))  m = extend-context nm a m
under-abs _ m = m

extend-context* : Telescope → TC A → TC A
extend-context* []              x = x
extend-context* ((n , t) ∷ tel) x = extend-context n t (extend-context* tel x)

new-meta : Term → TC Term
new-meta ty = do
  mv ← check-type unknown ty
  debug-print "tactic.meta" 70
    [ "Created new meta " , term-err mv , " of type " , term-err ty ]
  pure mv

new-meta′ : Term → TC (Meta × Term)
new-meta′ ty = do
  tm@(meta mv _) ← check-type unknown ty
    where _ → type-error $ [ "impossible new-meta′" ]
  debug-print "tactic.meta" 70
    [ "Created new meta " , term-err tm , " of type " , term-err tm ]
  pure (mv , tm)

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

infer-hidden : (m : ℕ) → Args → Args
infer-hidden 0       xs = xs
infer-hidden (suc n) xs = harg unknown ∷ infer-hidden n xs

infer-tel : Telescope → Args
infer-tel = map (map (λ _ → unknown) ∘ˢ snd)

get-name : Term → Maybe Name
get-name (def x _) = just x
get-name (con x _) = just x
get-name _ = nothing

“refl” : Term
“refl” = def (quote reflₚ) []

“Path” : Term → Term → Term → Term
“Path” A x y = def (quote Path) (unknown h∷ A v∷ x v∷ y v∷ [])

resetting : TC A → TC A
resetting k = run-speculative ((_, false) <$> k)

pi-view-path : Term → Telescope
pi-view-path (pi x (abs n y)) = (n , x) ∷ pi-view-path y
pi-view-path (def (quote Pathᴾ) (_ h∷ lam _ (abs n y) v∷ _ v∷ _ v∷ [])) =
  (n , argN (quoteTerm I)) ∷ pi-view-path y
pi-view-path _ = []

tel→pats : ℕ → Telescope → Patterns
tel→pats skip [] = []
tel→pats skip ((_ , arg ai _) ∷ tel) = arg ai (var (skip + length tel)) ∷ tel→pats skip tel

tel→args : ℕ → Telescope → Args
tel→args = with-full-tank worker where
  worker : (fuel : ℕ) → ℕ → Telescope → Args
  worker 0 _ _ = []
  worker (suc fuel) skip [] = []
  worker (suc fuel) skip ((_ , arg ai t) ∷ tel) = arg ai
    (tel→lam imp (var (skip + length tel + length imp) (worker fuel 0 imp)))
    ∷ worker fuel skip tel
    where
      imp = pi-impl-view t .fst

wait-for-args : Args → TC Args
wait-for-type : Term → TC Term

wait-for-type (var x args) = var x <$> wait-for-args args
wait-for-type (con c args) = con c <$> wait-for-args args
wait-for-type (def f args) = def f <$> wait-for-args args
wait-for-type (lam v (abs x t)) = pure (lam v (abs x t))
wait-for-type (pat-lam cs args) = pure (pat-lam cs args)
wait-for-type (pi (arg i a) (abs x b)) = do
  a ← wait-for-type a
  b ← wait-for-type b
  pure (pi (arg i a) (abs x b))
wait-for-type (agda-sort s) = pure (agda-sort s)
wait-for-type (lit l) = pure (lit l)
wait-for-type (meta x x₁) = block-on-meta x
wait-for-type unknown = pure unknown

wait-for-args [] = pure []
wait-for-args (arg i a ∷ xs) = ⦇ ⦇ (arg i) (wait-for-type a) ⦈ ∷ wait-for-args xs ⦈

wait-just-a-bit : Term → TC Term
wait-just-a-bit (meta m _) = block-on-meta m
wait-just-a-bit tm = pure tm

blocking-meta : Term → Maybe Blocker
blocking-meta* : Args → Maybe Blocker

blocking-meta (var x as)       = nothing
blocking-meta (con c as)       = nothing
blocking-meta (def f as)       = blocking-meta* as
blocking-meta (lam v t)        = nothing
blocking-meta (pat-lam _ as)   = blocking-meta* as
blocking-meta (pi a (abs _ b)) = blocking-meta b
blocking-meta (agda-sort s)    = nothing
blocking-meta (lit l)          = nothing
blocking-meta (meta x _)       = just (blocker-meta x)
blocking-meta unknown          = nothing

blocking-meta* (arg (arg-info visible _)   tm ∷ _ ) = blocking-meta tm
blocking-meta* (arg (arg-info instance′ _) tm ∷ _ ) = blocking-meta tm
blocking-meta* (arg (arg-info hidden _)    tm ∷ as) = blocking-meta* as
blocking-meta* [] = nothing

reduceB : Term → TC Term
reduceB tm = do
  tm′ ← reduce tm
  case blocking-meta tm′ of λ where
    (just b) → blockTC b
    nothing  → pure tm′

unapply-path : Term → TC (Maybe (Term × Term × Term))
unapply-path red@(def (quote Pathᴾ) (l h∷ T v∷ x v∷ y v∷ [])) = do
  domain ← new-meta (def (quote Type) (l v∷ []))
  ty ← pure (def (quote Path) (domain v∷ x v∷ y v∷ []))
  debug-print "tactic" 50
    [ "(no reduction) unapply-path: got a "
    , term-err red
    , " but I really want it to be "
    , term-err ty
    ]
  unify red ty
  pure (just (domain , x , y))
unapply-path tm = reduce tm >>= λ where
  tm@(meta _ _) → do
    dom ← new-meta (def (quote Type) (unknown v∷ []))
    l ← new-meta dom
    r ← new-meta dom
    unify tm (def (quote Path) (dom v∷ l v∷ r v∷ []))
    traverse wait-for-type (l ∷ r ∷ [])
    pure (just (dom , l , r))
  red@(def (quote Pathᴾ) (l h∷ T v∷ x v∷ y v∷ [])) → do
    domain ← new-meta (def (quote Type) (l v∷ []))
    ty ← pure (def (quote Path) (domain v∷ x v∷ y v∷ []))
    debug-print "tactic" 50
      [ "unapply-path: got a "
      , term-err red
      , " but I really want it to be "
      , term-err ty
      ]
    unify red ty
    pure (just (domain , x , y))
  _ → pure nothing

get-boundary : Term → TC (Maybe (Term × Term))
get-boundary tm = unapply-path tm >>= (pure ∘ˢ (snd <$>_))


debug! : Term → TC A
debug! tm = type-error [ "[DEBUG]: " , term-err tm ]

quote-repr-macro : Bool → A → Term →  TC ⊤
quote-repr-macro norm? a hole = do
  tm ← quoteTC a
  repr ← (if norm? then normalise else pure) tm >>= quoteTC
  type-error [ "The term\n  "
    , term-err tm
    , "\nHas quoted representation\n  "
    , term-err repr ]

macro
  quote-repr! : {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr! = quote-repr-macro false

  quote-repr-norm! : {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr-norm! = quote-repr-macro true

unify-loudly : Term → Term → TC ⊤
unify-loudly a b = do
  debug-print "tactic" 50 [ term-err a , " =? " , term-err b ]
  unify a b

pattern nat-lit n =
  def (quote From-ℕ.fromNat) (_ ∷ _ ∷ _ ∷ lit (nat n) v∷ _)

suc-term : Term → Term
suc-term (lit (nat n)) = lit (nat (suc n))
suc-term t = con (quote suc) (t v∷ [])

pred-term : Term → Maybe Term
pred-term (con (quote suc) (x v∷ [])) = just x
pred-term (lit (nat n)) with n
... | suc k = just (lit (nat k))
... | _ = nothing
pred-term _ = nothing

private
  _+′_ : ℕ → ℕ → ℕ
  m     +′ 0     = m
  0     +′ n     = n
  suc m +′ suc n = suc (suc (m +′ n))

plus-term : Term → Term → Term
plus-term (nat-lit 0) (nat-lit n) = lit (nat n)
plus-term (nat-lit m) (nat-lit 0) = lit (nat m)
plus-term (lit (nat 0)) (lit (nat n)) = lit (nat n)
plus-term (lit (nat m)) (lit (nat 0)) = lit (nat m)
plus-term (lit (nat m)) (lit (nat n)) = lit (nat (m + n))
plus-term x y = def (quote _+′_) (x v∷ y v∷ [])

-- working under lambda

leave : Telescope → Term → Term
leave [] = id
leave ((na , arg as _) ∷ xs) = leave xs ∘ˢ lam (arg-vis as) ∘ˢ abs na

enter : Telescope → TC A → TC A
enter [] = id
enter ((na , ar) ∷ xs) = enter xs ∘ˢ extend-context na ar


strip-invisible : Term → Term × List Arg-info
strip-invisible (pi (varg a) b) = pi (varg a) b , []
strip-invisible (pi (arg ai a) (abs s b)) =
  second (ai ∷_) $ strip-invisible b
strip-invisible t = t , []

-- returns free variables as de Bruijn indices in the _current_ context
-- same order as in input term, has duplicates
fv-dup : Term → List ℕ
fv-dup = go 0 where
  go : ℕ → Term → List ℕ
  go* : ℕ → Args → List ℕ

  go nbind (var v args) =
    if nbind <ᵇ suc v
       then (v ∸ nbind) ∷_
       else id
     $ go* nbind args
  go nbind (con _ args) = go* nbind args
  go nbind (def _ args) = go* nbind args
  go nbind (lam _ (abs _ x)) = go (suc nbind) x
  go nbind (pi (arg _ x) (abs _ y)) =
    go nbind x List.++ go (suc nbind) y
  go nbind (agda-sort (set x)) = go nbind x
  go nbind (agda-sort (prop x)) = go nbind x
  go _   _ = []

  go* _ [] = []
  go* nbind (arg _ x ∷ xs) =
    go nbind x List.++ go* nbind xs

fv     = nub-slow _==_ ∘ˢ fv-dup
fv-ord = nub-unsafe _==_ ∘ˢ insertion-sort (λ m n → m <ᵇ suc n) ∘ˢ fv-dup
