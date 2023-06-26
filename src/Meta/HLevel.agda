{-# OPTIONS --safe #-}
-- -vtactic.hlevel:20 -vtc.def:10
module Meta.HLevel where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel public
open import Foundations.Pi
open import Foundations.Sigma

open import Meta.Foldable
open import Meta.Literals.FromNat
open import Meta.Literals.FromProduct
open import Meta.Literals.FromString
open import Meta.Reflection

open import Structures.n-Type

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Instances.Foldable
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom
open import Data.Maybe.Base
open import Data.Nat.Base

{-
Tactic for generating readable h-level proofs automatically. Contains an
essential reimplementation of the instance search mechanism, with
support for arbitrary level offsets (`level-minus) and searching under
binders (`search-under). Ambiguity is explicitly supported: the first
goal for which we can complete a proof tree is the one we go with.

The tactic works in a naÏve way, trying h-level lemmas until one
succeeds. There are three ways of making progress: Using a *projection
hint*, using a *decomposition hint*, or by falling back to instance
selection. The instance selection fallback is self-explanatory.

Projection hints handle the situation is-hlevel (X .p) n, where X
inhabits a record that contains evidence of its hlevel. If there is a
projection hint with `underlying-type == p`, then we use `has-level
(get-argument (X .p))` as the solution. Being a base case, projection
hints also handle raising h-levels: If `get-level (X .p) < n`, we solve
by raising `has-level ...` the appropriate amount.

Decomposition hints are slightly more interesting. Decomposition hints
apply to a type, say P, and instruct the tactic on how to build an
application of type (is-hlevel P n). The way this application is built
is customizable.

Finding rules
-------------

Rules are found using instance search, specifically for the
'hlevel-decomposition' and 'hlevel-projection' types. The
hlevel-projection type is flat, so the runtime of
projection-decomposition is *linear in the number of possible
projections*.

The hlevel-decomposition type is more interesting, since it is indexed
by the type that it can decompose. That way, we can use Agda's own
instance selection mechanism to narrow down to relevant decompositions.

Nondeterminism
--------------

In case more than one projection and/or decomposition hint is possible,
they will all be tried in order. This allows the tactic to generate
sensible-looking code, by trying simpler decompositions first. As an
example, the non-dependent lemmas for → and × will be tried before those
for Π and Σ, just like a human would.
-}

-- | Specifies how an argument should be filled in during elaboration of
-- an h-level lemma.
data Arg-spec : Type where
  `level-minus  : (n : ℕ) → Arg-spec
  -- ^ Insert the level we're solving for minus the given offset (note
  -- that this is the wonky subtraction operation, "monus") at this
  -- argument position

  `search-under : (n : ℕ) → Arg-spec
  -- ^ Recursively search for an h-level witness, under @n@ visible
  -- lambdas. This is suitable for lemmas of type
  -- (∀ x y z → is-hlevel ...) → is-hlevel ...

  `meta         : Arg-spec
  -- ^ Insert a meta at this argument position. No search will be
  -- performed for this meta, so it must be solved from the context in
  -- which the lemma is used.

-- Common patterns: Keep the level, search in the current scope.
pattern `search = `search-under 0
pattern `level = `level-minus 0

-- | A specification for how to decompose the type @T@ into
-- sub-components, to establish an h-level result.
data hlevel-decomposition {ℓ} (T : Type ℓ) : Type where
  decomp
    : (h-level-lemma : Name) (arguments : List Arg-spec)
    → hlevel-decomposition T
  -- To prove that T has a given h-level, we can invoke the
  -- @h-level-lemma@ with the specified @arguments@.

-- | How to decompose an application of a record selector into something
-- which might have an h-level.
record hlevel-projection (proj : Name) : Type where
  field
    has-level : Name
    -- ^ The name of the h-level lemma. It must be sufficient to apply
    -- this name to the argument (see get-argument below); arg specs are
    -- not supported.
    get-level : Term → TC Term
    -- ^ Given an application of underlying-type, what h-level does this
    -- type have? Necessary for computing lifts.
    get-argument : List (Arg Term) → TC Term
    -- ^ Extract the argument out from under the application.
{-
Using projections
-----------------

Projection decomposition happens as follows; suppose we have some
neutral

  n = def (quote X) as

in order, every 'hlevel-projection' instance definition will be tried;
Let us call a generic instance I. If I.underlying-type == X, then we'll
use this instance, otherwise, we fail (i.e. backtrack and try another
projection).

To use this instance, the get-level and get-argument functions are
involved; get-argument must take 'as' and return some representative
sub-expression e. get-level will receive e's inferred type and must
return the h-level of the type n. Finally, we return

  I.has-level (get-argument e),

possibly wrapped in (k - get-level (get-argument e)) applications of
is-hlevel-suc.
-}

open hlevel-projection
private
  -- Throw an empty type error to try another alternative, stating the
  -- purpose of backtracking for debugging:
  backtrack : ∀ {ℓ} {A : Type ℓ} → List ErrorPart → TC A
  backtrack note = do
    debugPrint "tactic.hlevel" 10 $ "Backtracking search... " ∷ note
    typeError $ "Search hit a dead-end: " ∷ note

  -- A list of names which we should not reduce while trying to invert
  -- an application of is-hlevel/is-prop/is-set into an 'underlying
  -- type' and level arguments.
  atoms : List Name
  atoms = [ quote is-of-hlevel
          , quote is-prop
          , quote is-set
          , quote _≃_
          ]

  pattern nat-lit n =
    def (quote Number.fromNat) (_ ∷ _ ∷ _ ∷ lit (nat n) v∷ _)

  -- Decompose an application of is-hlevel and/or one of the other
  -- 'hlevel-types' into its constituent parts. Invariant:
  --
  --    decompose-is-hlevel′ t = (n , a) ⊢ t = is-of-hlevel n a
  decompose-is-hlevel′ : Term → TC (Term × Term)

  -- Infer the type of the given term, and decompose it according to
  -- decompose-is-hlevel′.
  decompose-is-hlevel : Term → TC (Term × Term)
  decompose-is-hlevel goal = do
    ty ← withReduceDefs (false , atoms) $ inferType goal >>= reduce
    decompose-is-hlevel′ ty

  decompose-is-hlevel′ ty = do
    def (quote is-of-hlevel) (_ ∷ lv v∷ ty v∷ []) ← pure ty
      where
        -- Handle the ones with special names:
        def (quote is-set) (_ ∷ ty v∷ []) → do
          ty ← wait-just-a-bit ty
          pure (quoteTerm 2 , ty)

        def (quote is-prop) (_ ∷ ty v∷ []) → do
          ty ← wait-just-a-bit ty
          pure (quoteTerm 1 , ty)

        def (quote is-contr) (_ ∷ ty v∷ []) → do
          ty ← wait-just-a-bit ty
          pure (quoteTerm 0 , ty)

        _ → backtrack "Goal type isn't is-hlevel"

    -- To support having bare hlevel! in the source file, we need to
    -- block decomposition on having a rigid-ish type at the
    -- top-level. Otherwise the first hint that matches will get
    -- matched endlessly until we run out of fuel!
    ty ← wait-just-a-bit ty
    lv ← wait-just-a-bit lv
    pure (lv , ty)

{-
Lifting n-Types
---------------

The n-types are the leaves of the hlevel solving process, so they're
pretty much our only opportunity to adjust levels in a big way. Suppose
you have

  T = def (quote X) as

with
  get-level (get-argument T) = n
  w : is-of-hlevel n T

but what you want is a witness of is-of-hlevel (k + n) T, where k is some
numeral? Well, the solution is obvious: we can compute k - n and lift
T's witness (k - n) levels. Right?

No: we're dealing with potential open naturals, so we have to be careful
about performing ‘symbolic’ subtractions. The way we do this is with,
essentially, a loop: If w doesn't work, then try

  is-hlevel-suc n w : is-hlevel (suc n) T

until you reach a sucᵏ n = k + n. Actually, slightly more efficient, we
keep around a counter k′ for the number of tries, and transfer successors
from the wanted level (k + n) until is-of-hlevel-+ n (sucᵏ′ n) w works.
-}
  lift-sol : Term → Term → ℕ → Term
  lift-sol tm _ 0 = tm
  lift-sol tm l1 l = def (quote is-of-hlevel-+) (l1 v∷ lit (nat l) v∷ tm v∷ [])

  pred-term : Term → Maybe Term
  pred-term (con (quote suc) (x v∷ [])) = just x
  pred-term (lit (nat n)) with n
  ... | suc k = just (lit (nat k))
  ... | _ = nothing
  pred-term _ = nothing

  lifting-loop : (fuel : ℕ) → ℕ → Term → Term → Term → Term → TC ⊤
  lifting-loop zero _ _ _ _ _ = backtrack "Lifting loop ran out of fuel"
  lifting-loop (suc fuel) it solution goal l1 l2 =
    let's-hope <|> do
      (just l2′) ← pred-term <$> normalise l2 where
        nothing → backtrack "Lifting loop reached its end with no success"
      lifting-loop fuel (suc it) solution goal l1 l2′
    where
      let's-hope : TC ⊤
      let's-hope = do
        debugPrint "tactic.hlevel" 30 $ "Lifting loop: Trying " ∷ termErr (lift-sol solution l1 it) ∷ " for level " ∷ termErr l2 ∷ []
        unify goal (lift-sol solution l1 it)
    -- con (quote suc) (

  -- Projection decomposition.
  treat-as-n-type : ∀ {n} → hlevel-projection n → Term → TC ⊤
  treat-as-n-type projection goal = do
    -- First we must be looking at a goal which is of the type is-hlevel
    -- A n. We'll need both n and A.
    (wanted-level , ty) ← decompose-is-hlevel goal
    debugPrint "tactic.hlevel" 10 $
      "Attempting to treat as " ∷ termErr wanted-level ∷ "-Type: " ∷ termErr ty ∷ []
    ty ← reduce ty

    -- Reduce the type to whnf and check whether the outermost term
    -- constructor is an application of the projection we're looking
    -- for.
    def namen args ← returnTC ty
      where what → backtrack $ "Thing isn't an application, it is " ∷ termErr what ∷ []

    it ← projection .get-argument args

    -- And compute the level of the projected thing, in addition to a
    -- numeral form of the wanted level.
    actual-level ← inferType it >>= projection .get-level

    debugPrint "tactic.hlevel" 10 $
      "... but it's actually a(n) " ∷ termErr actual-level ∷ "-Type" ∷ []

    lv ← normalise wanted-level
    lv′ ← normalise actual-level
    lifting-loop 10000 0 (def (projection .has-level) (it v∷ [])) goal lv′ lv

    commitTC

  -- Fall back to Agda's instance search mechanism. This isn't as
  -- straightforward as just using the 'hlevel' function for a couple of
  -- reasons.
  use-instance-search : Bool → Term → TC ⊤
  use-instance-search has-alts goal = runSpeculative $ do
    (lv , ty) ← decompose-is-hlevel goal
    solved@(meta mv _) ←
      new-meta (def (quote is-of-hlevel) (lv v∷ ty v∷ [])) where _ → backtrack []
    instances ← getInstances mv

    t ← quoteTC instances
    debugPrint "tactic.hlevel" 10 $
      "Using instance search for\n" ∷ termErr ty ∷
      "\nFound candidates\n " ∷ termErr t ∷ []

    -- We actually want to manage the instance searching ourselves,
    -- sorta, to avoid getting into situations where the macro has
    -- committed to instance search but Agda will disagree with it.
    let
      go : List Term → TC (⊤ × Bool)
      go = λ where
        -- If there is *exactly* one instance candidate for this goal,
        -- then we can go ahead and solve it. That's because having
        -- exactly one instance means Agda will solve using that
        -- instance!
        (x ∷ []) → do
          -- Note that, since getInstances works by creating a new meta,
          -- we have to commit to the instance ourselves.
          unify solved x
          withReduceDefs (false , quote hlevel ∷ []) $ withReconstructed true $
            unify goal (def (quote hlevel) (lv v∷ []))
          pure (tt , true)

        -- If there are any more alternatives to be tried after this
        -- one, then we fail (backtrack). Otherwise, we discard the TC
        -- state but indicate success: this will cause the meta to be
        -- solved with an interaction point (if using
        -- elaborate-and-give).
        [] → if has-alts
          then backtrack "No possible instances, but have other decompositions to try"
          else pure (tt , false)

        _ → backtrack "Too many possible instances; will not use instance search for this goal"
    go instances

  -- Entry point for calling the tactic.
  search : Bool → Term → ℕ → Term → TC ⊤
  -- Give up if we're out of fuel:
  search has-alts _     zero    goal = unify goal unknown

  -- Actual main loop: try using the hints database, try treating the
  -- goal as an n-type, fall back to instance search.
  search has-alts level (suc n) goal =
    use-projections
      <|> use-hints
      <|> use-instance-search has-alts goal
      <|> typeError "Search failed!!"
    where
      open hlevel-projection

      -- Nondeterministically use a projection for establishing the
      -- result. This follows the approach described in [Using
      -- projections].
      use-projections : TC ⊤
      use-projections = do
        def qn _ ← (snd <$> decompose-is-hlevel goal) >>= reduce
          where _ → backtrack "Term is not headed by a definition; ignoring projections."

        goalt ← inferType goal
        debugPrint "tactic.hlevel" 20 $
          "Will attempt to use projections for goal\n  " ∷ termErr goalt ∷ []

        (solved , instances) ← runSpeculative $ do
          solved@(meta mv _) ← new-meta (def (quote hlevel-projection) (lit (name qn) v∷ []))
            where _ → typeError (termErr goal ∷ [])

          -- If there are some hints, then great, otherwise we discard
          -- the TC state.
          (x ∷ xs) ← getInstances mv
            where [] → pure ((unknown , []) , false)

          pure ((solved , x ∷ xs) , true)

        nondet (eff List) instances λ a → do
          projection ← unquoteTC {A = hlevel-projection qn} a
          ty ← withReduceDefs (false , atoms) (inferType goal >>= reduce)
          debugPrint "tactic.hlevel" 20 $
            "Outer type: " ∷ termErr ty ∷ []
          treat-as-n-type projection goal >> unify solved a

      -- Get rid of any invisible binders that lead the term.
      remove-invisible : Term → Term → TC Term
      remove-invisible
        (lam _ (abs _ t))
        (pi (arg (arg-info invisible _) _) (abs _ ret))
        = remove-invisible t ret
      remove-invisible inner _ = pure inner

      -- Search using decompositions involves manipulating the scope,
      -- which is why it's spread over so many functions, and even then,
      -- some are too big.

      -- Wrap the given term in a series of visible lambdas.
      wrap-lams : ℕ → Term → Term
      wrap-lams zero r = r
      wrap-lams (suc x) r = lam visible $ abs "a" $ wrap-lams x r

      -- Compute a continuation which extends the context by n visible
      -- variables, all typed 'unknown'.
      extend-n : ∀ {ℓ} → ℕ → TC ((A : Type ℓ) → TC A → TC A)
      extend-n zero = pure λ _ x → x
      extend-n (suc n) = do
        rest ← extend-n n
        lift mv ← rest (Lift _ Term) $ lift <$> new-meta unknown
        let domain = arg (arg-info visible (modality relevant quantity-ω)) mv
        pure λ a k → rest a $ extendContext "a" domain $ k

      -- Given a list of argument specs, actually unify the goal with
      -- the solution of decomposition, and call a continuation to
      -- perform any outstanding searches.
      gen-args
        : Bool              -- ^ Are there any alternatives after this one?
        → Term              -- ^ What level are we searching for?

        → Name              -- ^ Name of the lemma,
        → List Arg-spec     -- ^ and the arguments we should invent.

        → List (Arg Term)
        -- ^ Accumulator: computed arguments (criminally, in reverse
        -- order)
        → TC ⊤
          -- ^ Accumulator/continuation: what do we need to do after
          -- unifying the goal with the lemma?. This is both
          -- continuation (it can be used to run something after the
          -- arguments are built) and accumulator (searching recursively
          -- is done last).
        → TC ⊤              -- ^ Returns nada
      gen-args has-alts level defn [] accum cont = do
        -- If we have no arguments to generate, then we can go ahead and
        -- use the accumulator as-is.
        unify goal (def defn (reverse-fast accum))
        debugPrint "tactic.hlevel" 10 $
          "Committed to solution: " ∷ termErr (def defn (reverse accum)) ∷ []
        cont

      gen-args has-alts level defn (x ∷ args) accum cont with x
      -- If we got asked for the level without an adjustment (i.e. monus
      -- by zero), then we may as well not bother *trying* to adjust it.
      -- Saves a bit of computation.
      ... | `level-minus 0 = gen-args has-alts level defn args (level v∷ accum) cont
      -- If we have to insert the level minus some offset, then we need
      -- to do the computation:
      ... | `level-minus n@(suc _) =
        do
          level ← normalise level
          debugPrint "tactic.hlevel" 10 $
            "Hint demands offset, performing symbolic monus, subtracting from\n  " ∷ termErr level ∷ []
          level′′ ← monus level n
          -- Reduce otherwise we get Number.fromNat as the term
          gen-args has-alts level defn args (level′′ v∷ accum) cont
        where
          -- A 'symbolic' monus function. If we're looking at an actual
          -- number, then we can just do the computation in TC, but
          -- otherwise we have to reimplement the builtin subtraction,
          -- where the minuend is a *term* rather than a number. In
          -- addition to being a bad operation (monus, grr), it's
          -- *partial*. We can end up backtracking while subtracting.
          monus : Term → ℕ → TC Term
          monus (lit (nat n)) k = pure $ lit (nat (n - k))
          monus tm zero = pure tm
          monus thezero@(con (quote zero) []) (suc it) = pure thezero
          monus (con (quote suc) (x v∷ [])) (suc it) = do
            x ← reduce x
            monus x it
          monus tm (suc it) = do
            debugPrint "tactic.hlevel" 10 $ "Dunno how to take 1 from " ∷ termErr tm ∷ []
            typeError []

      -- Insert a metavariable, to be solved by Agda. It'd be sad if the
      -- macro handled everything!
      ... | `meta = gen-args has-alts level defn args (unknown v∷ accum) cont

      ... | `search-under under = do
        -- To search under some variables, we work in a scope extended
        -- by 'under'-many variables. The metavariable lives in that
        -- scope, so we have to quantify over the variables we
        -- introduced to use it outside, i.e., in the actual (outer)
        -- search problem.
        debugPrint "tactic.hlevel" 10 $ "Going under " ∷ termErr (lit (nat under)) ∷ []
        gounder ← extend-n under
        mv ← gounder Term $ do
          debugPrint "tactic.hlevel" 10 $ "In extended context"
          new-meta unknown
        debugPrint "tactic.hlevel" 10 $ "Metavariable: " ∷ termErr (wrap-lams under mv) ∷ []
        -- After we've put the mv wrapped under some lambdas in the
        -- argument list,
        gen-args has-alts level defn args (wrap-lams under mv v∷ accum) $ do
          -- On our way back up, we do any more searching that needed to
          -- get done, and..
          cont
          -- go back under the new scope to recursively search for
          -- levels.
          gounder ⊤ $ search has-alts unknown n mv

      -- Try all the candidate hints in order. This is a version of
      -- 'nondet' which additionally threads whether we're looking at
      -- last alternative.
      use-decomp-hints : (Term × Term) → Term → List Term → TC (⊤ × Bool)
      use-decomp-hints (lv , goal-ty) solved (c1 ∷ cs) = do
        ty ← inferType c1
        c1′ ← reduce c1
        (remove-invisible c1′ ty >>= λ where

          -- If we have an actual decomp constructor, then we can try
          -- using its argument specification to construct a little
          -- h-level lemma
          (con (quote decomp) (_ ∷ _ ∷ nm v∷ argspec v∷ [])) → do
            debugPrint "tactic.hlevel" 10 $
              "Using " ∷ termErr nm ∷ " decomposition for:\n  "
              ∷ termErr (def (quote is-of-hlevel) (lv v∷ goal-ty v∷ [])) ∷ []

            nm′ ← unquoteTC nm
            argsp ← unquoteTC argspec
            -- Generate the argument spine, and discard the instance
            -- search meta.
            gen-args (not (length cs == 0)) lv nm′ argsp [] (returnTC tt)
            unify solved c1

            pure (tt , true)

          -- It's possible that this particular hint was a bust, i.e.
          -- because someone wasn't being careful with what
          -- hlevel-decomposition instances they've defined. That's no
          -- matter: we can just ignore it.
          _ → backtrack "Non-canonical hint")
          -- If we didn't manage to get the hint to work, for any
          -- reason, try again with the rest of the hints.
          <|> use-decomp-hints (lv , goal-ty) solved cs

      use-decomp-hints (_ , goal-ty) _ [] =
        backtrack $ "Ran out of decomposition hints for " ∷ termErr goal-ty ∷ []

      -- Using the hints involving querying Agda for potential
      -- instances, then trying each in order.
      use-hints : TC ⊤
      use-hints = runSpeculative $ do
        (lv , ty) ← decompose-is-hlevel goal

        -- Note that if the type here is a metavariable, the tactic is..
        -- loopy.
        pure ty >>= λ where
          (meta m _) → do
            debugPrint "tactic.hlevel" 10
              "Type under is-hlevel is metavariable, blocking to avoid infinite loop"
            blockOnMeta m
          _ → pure tt

        -- Create a meta of type hlevel-decomposition to find any possible hints..
        solved@(meta mv _) ← new-meta (def (quote hlevel-decomposition) (ty v∷ []))
          where _ → typeError (termErr ty ∷ [])
        instances ← getInstances mv

        t ← quoteTC instances
        debugPrint "tactic.hlevel" 10 $
          "Finding decompositions for\n" ∷
          termErr ty ∷
          "\nFound candidates\n " ∷
          termErr t ∷ []

        -- And try using the hints.
        use-decomp-hints (lv , ty) solved instances

  -- At the top-level, our goal doesn't need to have literally the type
  -- is-hlevel A n. It can be under any number of Πs, both implicit and
  -- explicit. This means that a goal like (∀ x → is-hlevel T n) can be
  -- solved using just hlevel!, rather than λ _ → hlevel!. Of course,
  -- the effect is the same.
  decompose-is-hlevel-top
    : ∀ {ℓ} {A : Type ℓ}
    → Term → TC (Term × Term × (TC A → TC A) × (Term → Term))
  decompose-is-hlevel-top goal =
    do
      ty ← withReduceDefs (false , atoms) $
        (inferType goal >>= reduce) >>= wait-just-a-bit
      go ty
    where
      go : Term → TC _
      go (pi (arg as at) (abs vn cd)) = do
        (hlevel , inner , enter , leave) ← go cd
        pure $ hlevel , inner , extendContext vn (arg as at) , λ t → lam (arg-vis as) (abs vn t)
      go tm = do
        (hlevel , inner) ← decompose-is-hlevel′ tm
        pure $ hlevel , inner , (λ x → x) , (λ x → x)

-- This is public so it's usable in tactic attributes. It decomposes the
-- top-level goal type and enters the search loop.
hlevel-tactic-worker : Term → TC ⊤
hlevel-tactic-worker goal = do
  ty ← withReduceDefs (false , atoms) $ inferType goal >>= reduce
  debugPrint "tactic.hlevel" 10 $ "Target type: " ∷ termErr ty ∷ []
  (lv , ty , enter , leave) ← decompose-is-hlevel-top goal <|>
    typeError
      ( "Goal type is not of the form ``is-hlevel A n'':\n"
      ∷ termErr ty
      ∷ [])

  -- 10 units of fuel isn't too many but it's enough for any realistic
  -- use-case. Note the scope nonsense: we have to 'enter' to get under
  -- the Πs (extend the scope with their argument types), then 'leave'
  -- (wrap in lambdas) to get back out.
  solved ← enter $ do
    goal′ ← new-meta (def (quote is-of-hlevel) (lv v∷ ty v∷ []))
    search false lv 10 goal′
    pure goal′
  unify goal (leave solved)

-- Entry points to the macro
----------------------------
macro hlevel! = hlevel-tactic-worker

private variable
  ℓ ℓ′ ℓa ℓb ℓc ℓd : Level
  T : Type ℓ
  A : Type ℓa
  B : A → Type ℓb
  C : (a : A) (b : B a) → Type ℓc
  D : (a : A) (b : B a) (c : C a b) → Type ℓd
  n : HLevel

-- In addition to using the macro as a.. well, macro, it can be used as
-- a tactic argument, to replace instance search by the more powerful
-- decomposition-projection mechanism of the tactic. We provide only
-- some of the most common helpers:
el! : (A : Type ℓ) {@(tactic hlevel-tactic-worker) hl : is-of-hlevel n A} → n-Type ℓ n
el! A {hl} = el A hl

prop-extₑ!
  : {B : Type ℓb}
    {@(tactic hlevel-tactic-worker) aprop : is-prop A}
    {@(tactic hlevel-tactic-worker) bprop : is-prop B}
  → (A → B) → (B → A)
  → A ≃ B
prop-extₑ! {aprop} {bprop} = prop-extₑ aprop bprop

Σ-prop-path!
  : {@(tactic hlevel-tactic-worker) bxprop : ∀ x → is-prop (B x)}
  → {x y : Σ A B}
  → x .fst ＝ y .fst
  → x ＝ y
Σ-prop-path! {bxprop} = Σ-prop-path bxprop

prop!
  : {A : I → Type ℓ} {@(tactic hlevel-tactic-worker) aip : is-prop (A i0)}
  → {x : A i0} {y : A i1}
  → PathP A x y
prop! {A} {aip} {x} {y} =
  is-prop→pathP (λ i → coe0→i (λ j → is-prop (A j)) i aip) x y

open hlevel-projection

-- Hint database bootstrap
--------------------------
-- This instance block contains most of the decompositions we have
-- defined in the dependencies of this module.

instance
  decomp-lift : hlevel-decomposition (Lift ℓ′ A)
  decomp-lift = decomp (quote Lift-is-of-hlevel) (`level ∷ `search ∷ [])

  -- Non-dependent Π and Σ for readability (lol) first
  decomp-fun : {B : Type ℓb} → hlevel-decomposition (A → B)
  decomp-fun = decomp (quote fun-is-of-hlevel) (`level ∷ `search ∷ [])

  decomp-prod : {B : Type ℓb} → hlevel-decomposition (A × B)
  decomp-prod = decomp (quote ×-is-of-hlevel) (`level ∷ `search ∷ `search ∷ [])

  -- Dependent type formers:
  decomp-pi³ : hlevel-decomposition (∀ a b c → D a b c)
  decomp-pi³ = decomp (quote Π₃-is-of-hlevel) (`level ∷ `search-under 3 ∷ [])

  decomp-pi² : hlevel-decomposition (∀ a b → C a b)
  decomp-pi² = decomp (quote Π₂-is-of-hlevel) (`level ∷ `search-under 2 ∷ [])

  decomp-pi : hlevel-decomposition (∀ a → B a)
  decomp-pi = decomp (quote Π-is-of-hlevel) (`level ∷ `search-under 1 ∷ [])

  decomp-impl-pi : hlevel-decomposition (∀ {a} → B a)
  decomp-impl-pi = decomp (quote Π-is-of-hlevel-implicit) (`level ∷ `search-under 1 ∷ [])

  decomp-equiv-right : {B : Type ℓb} → hlevel-decomposition (A ≃ B)
  decomp-equiv-right = decomp (quote ≃-is-of-hlevel-right-suc) (`level-minus 1 ∷ `search ∷ [])

  decomp-equiv-left : {B : Type ℓb} → hlevel-decomposition (A ≃ B)
  decomp-equiv-left = decomp (quote ≃-is-of-hlevel-left-suc) (`level-minus 1 ∷ `search ∷ [])

  decomp-equiv : {B : Type ℓb} → hlevel-decomposition (A ≃ B)
  decomp-equiv = decomp (quote ≃-is-of-hlevel) (`level ∷ `search ∷ `search ∷ [] )

  decomp-sigma : hlevel-decomposition (Σ A B)
  decomp-sigma = decomp (quote Σ-is-of-hlevel) (`level ∷ `search ∷ `search-under 1 ∷ [])

  -- Path decomposition rules we have in scope. Note the use of
  -- nondeterminism: the following three instances both compete for
  -- solving the same goals --- but generally only one will be
  -- applicable. That way we don't have to juggle h-levels quite as
  -- much.
  decomp-path′ : {a b : A} → hlevel-decomposition (a ＝ b)
  decomp-path′ = decomp (quote path-is-of-hlevel′) (`level ∷ `search ∷ `meta ∷ `meta ∷ [])

  decomp-path : {a b : A} → hlevel-decomposition (a ＝ b)
  decomp-path = decomp (quote path-is-of-hlevel) (`level ∷ `search ∷ [])

  decomp-univalence : {A B : Type ℓ} → hlevel-decomposition (A ＝ B)
  decomp-univalence = decomp (quote ＝-is-of-hlevel) (`level ∷ `search ∷ `search ∷ [] )

  -- This one really ought to work with instance selection only, but
  -- Agda has trouble with the (1 + k + n) level in H-Level-n-Type. The
  -- decomposition here is a bit more flexible.
  decomp-ntype : hlevel-decomposition (n-Type ℓ n)
  decomp-ntype = decomp (quote n-Type-is-of-hlevel) (`level-minus 1 ∷ [])

  hlevel-proj-n-type : hlevel-projection (quote Carrier)
  hlevel-proj-n-type .has-level = quote carrier-is-tr
  hlevel-proj-n-type .get-level ty = do
    def (quote n-Type) (ell v∷ lv′t v∷ []) ← reduce ty
      where _ → backtrack $ "Type of thing isn't n-Type, it is " ∷ termErr ty ∷ []
    normalise lv′t
  hlevel-proj-n-type .get-argument (_ ∷ _ ∷ it v∷ []) = pure it
  hlevel-proj-n-type .get-argument _ = typeError []


-- Usage
private
  module _ {A : n-Type ℓ 2} {B : ⌞ A ⌟ → n-Type ℓ 3} where
    some-def = ⌞ A ⌟
    _ : is-of-hlevel 2 (⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟ → ⌞ A ⌟)
    _ = hlevel!

    _ : is-of-hlevel 3 (Σ some-def λ x → ⌞ B x ⌟)
    _ = hlevel!

    _ : ∀ a → is-of-hlevel 5 (⌞ A ⌟ × ⌞ A ⌟ × (ℕ → ⌞ B a ⌟))
    _ = hlevel!

    _ : ∀ a → is-of-hlevel 3 (⌞ A ⌟ × ⌞ A ⌟ × (ℕ → ⌞ B a ⌟))
    _ = hlevel!

    _ : is-of-hlevel 2 ⌞ A ⌟
    _ = hlevel!

    -- this one uses `H-Level-nType` instance which is compile-time only
    @0 _ : ∀ n → is-of-hlevel (suc n) (n-Type ℓ n)
    _ = hlevel!

    _ : ∀ n (x : n-Type ℓ n) → is-of-hlevel (2 + n) ⌞ x ⌟
    _ = λ n x → hlevel!
