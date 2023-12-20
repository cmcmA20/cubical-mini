{-# OPTIONS --safe #-}
-- -vtactic.search:20 -vtc.def:10
module Meta.Search.Base where

open import Foundations.Base

open import Meta.Effect.Foldable
open import Meta.Literals.FromProduct
  public
open import Meta.Reflection.Base

open import Data.Bool.Base as Bool
open import Data.Bool.Base
  using (false; true)
  public
open import Data.Empty.Base
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Instances.FromNat
  public
open import Data.List.Base as List
open import Data.List.Operations as List
open import Data.List.Instances.Foldable
open import Data.List.Instances.FromProduct
  public
open import Data.List.Instances.Idiom
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Sum.Base
open import Data.Sum.Base
  using (inl; inr)
  public
open import Data.Vec.Inductive.Operations.Computational as Vec

data Goal-strat : Type where
  none by-hlevel : Goal-strat

private variable
  ℓ : Level
  goal-strat : Goal-strat

private
  goal-strat-elim : {P : Goal-strat → Type ℓ} → P by-hlevel → P none → (gs : Goal-strat) → P gs
  goal-strat-elim x _ by-hlevel = x
  goal-strat-elim _ y none = y

  goal-strat-rec : {ℓ : Level} {A : Type ℓ} → A → A → Goal-strat → A
  goal-strat-rec = goal-strat-elim

  goal-is-stratified : Goal-strat → Type
  goal-is-stratified = goal-strat-rec ⊤ ⊥

  Selector : @0 ℕ → Type
  Selector = Fin

select-arg : Visibility → {@0 m : ℕ} → Selector m → Vec (Arg Term) m → TC Term
select-arg vis idx args = case Vec.lookup args idx of λ where
  (vis-arg v x) → do
    guard (v visibility=? vis)
    pure x
  _ → type-error "Bad argument selector"

Level-data : Goal-strat → Type
Level-data = goal-strat-rec Term ⊤

dummy-level : Level-data goal-strat
dummy-level {(none)} = tt
dummy-level {(by-hlevel)} = unknown

fixed-level : ℕ → Level-data goal-strat
fixed-level {(none)} _ = tt
fixed-level {(by-hlevel)} n = lit (nat n)

level-term : Level-data goal-strat → Term
level-term {(none)} _ = lit (string "dummy")
level-term {(by-hlevel)} = id

Goal-data : Type
Goal-data = Σ[ args-length ꞉ ℕ ] Selector args-length

record Tactic-desc (goal-name : Name) (goal-strat : Goal-strat) : Type where
  field
    args-length : ℕ
    goal-selector : Selector args-length
    level-selector
      : {w : goal-is-stratified goal-strat} → Selector args-length
    aliases
      : {w : goal-is-stratified goal-strat}
      → List (Name × ℕ × Goal-data)
    other-atoms : List Name
    instance-name   : Name
    instance-helper : Name
    upwards-closure : {w : goal-is-stratified goal-strat} → Maybe Name
    -- ^ it should have a following signature
    --   (h₀ h₁ : HLevel) → whatever h₀ A → whatever (h₁ + h₀) A

  atoms : List Name
  atoms = goal-name ∷ other-atoms

open Tactic-desc

data Arg-spec : Goal-strat → Type where
  `level-suc    : Arg-spec by-hlevel
  `level-minus  : (n : ℕ) → Arg-spec by-hlevel
  `search-under : (n : ℕ) (subgoal : Name) → Arg-spec goal-strat
  `term         : Term → Arg-spec goal-strat

pattern `search sg  = `search-under 0 sg
pattern `level-same = `level-minus 0
pattern `meta       = `term unknown

data goal-decomposition
  {ℓ} (goal-name : Name) {goal-strat : Goal-strat}
  ⦃ @irr what : Tactic-desc goal-name goal-strat ⦄ (T : Type ℓ) : Type where
    decomp : (search-lemma : Name) (arguments : List (Arg-spec goal-strat))
           → goal-decomposition goal-name T

private
  goal-is-native : Bool → Type
  goal-is-native = Bool.rec ⊤ ⊥

record Struct-proj-desc
  (goal-name : Name) (goal-strat : Goal-strat)
  (carrier-name : Name) (goal-nat : Bool) : Type where
  field
    struct-name            : Name
    struct-args-length     : ℕ
    goal-projection        : Name
    projection-args-length : ℕ
    level-selector
      : {w : goal-is-stratified goal-strat}
      → ℕ ⊎ Selector struct-args-length
    carrier-selector       : Selector projection-args-length

open Struct-proj-desc

private variable
  A : Type ℓ
  goal-name carrier-name : Name
  goal-nat : Bool
  n : HLevel

backtrack : List ErrorPart → TC A
backtrack note = do
  debug-print "tactic.search" 10 $ "Backtracking search... " ∷ note
  type-error $ "Search hit a dead-end: " ∷ note

wait-for-principal-arg : Term → TC ⊤
wait-for-principal-arg t = go t where
  go : Term → TC ⊤
  go* : List (Arg Term) → TC ⊤

  go mv@(meta m _) = do
      debug-print "tactic.search" 30
        [ "wait-for-principal-arg: blocking on meta " , termErr mv
        , " in principal arguments of\n  " , termErr t
        ]
      block-on-meta m
  go (def d ds) = go* ds
  go _          = pure tt

  go* (arg (arg-info visible _) t ∷ as) = go t
  go* (_ ∷ as)                          = go* as
  go* []                                = pure tt

private
  args-list→args-vec : (desired-length : ℕ) → List (Arg Term) → TC (Vec (Arg Term) desired-length)
  args-list→args-vec 0 [] = pure []
  args-list→args-vec 0 (_ ∷ _) = backtrack "Too many arguments"
  args-list→args-vec (suc _) [] = backtrack "Too few arguments"
  args-list→args-vec (suc dl) (x ∷ xs) = do
    ih ← args-list→args-vec dl xs
    pure $ x ∷ ih

  compose-solution : Tactic-desc goal-name goal-strat → Bool → Level-data goal-strat → Term → Term
  compose-solution {goal-name} td instance? xlv ty = def target $ vec→list (go td xlv base-args) .fst where
    target = if instance? then td .instance-name else goal-name
    base-args = replace (td .goal-selector) (varg ty) $ Vec.replicate (td .args-length) (harg Term.unknown)
    go : ∀{gn gs} (td : Tactic-desc gn gs) → Level-data gs → Vec _ (td .args-length) → Vec _ (td .args-length)
    go {gs = by-hlevel} td xlv = replace (td .level-selector) (varg xlv)
    go {gs = none} _ _ = id

  compose-goal : Tactic-desc goal-name goal-strat → Level-data goal-strat → Term → Term
  compose-goal td = compose-solution td false

  compose-instance : Tactic-desc goal-name goal-strat → Level-data goal-strat → Term → Term
  compose-instance td = compose-solution td true

  decompose-alias
    : (actual : Name)
      (target : Term)
      (args : List (Arg Term))
    → Name × ℕ × Goal-data
    → TC (Level-data goal-strat × Term)
  decompose-alias actual target args (alias-name , lv , alias-args-length , sel) = do
    guard (actual name=? alias-name)
    argsᵥ ← args-list→args-vec alias-args-length args
    ty ← select-arg visible sel argsᵥ
    pure $ fixed-level lv , ty

  -- TODO refactor this abomination
  decompose-goal′ : Tactic-desc goal-name goal-strat → Term → TC (Level-data goal-strat × Term)
  decompose-goal′ {goal-name} {goal-strat = none} td ty = do
    def actual-goal-name args ← pure ty where
      x → backtrack
            [ "Goal type isn't an application of " , nameErr goal-name
            , "\nIt's " , termErr x ]
    guard (actual-goal-name name=? goal-name)
    argsᵥ ← args-list→args-vec (td .args-length) args
    ty ← select-arg visible (td .goal-selector) argsᵥ
    pure (tt , ty)
  decompose-goal′ {goal-name} {goal-strat = by-hlevel} td ty = do
    def actual-goal-name args ← pure ty where
      _ → backtrack [ "Goal type isn't an application of " , nameErr goal-name ]
    nondet (eff List) (td .aliases) (decompose-alias actual-goal-name ty args) <|> do
      guard (actual-goal-name name=? goal-name)
      argsᵥ ← args-list→args-vec (td .args-length) args
      ty ← select-arg visible (td .goal-selector) argsᵥ
      xlv ← select-arg visible (td .level-selector) argsᵥ
      pure (xlv , ty)

  decompose-goal : Tactic-desc goal-name goal-strat → Term → TC (Level-data goal-strat × Term)
  decompose-goal td goal = do
    ty ← with-reduce-defs (false , atoms td) $ infer-type goal >>= reduce
    decompose-goal′ td ty

  lift-sol : Tactic-desc goal-name by-hlevel → Term → Term → ℕ → TC Term
  lift-sol td tm _ 0  = pure tm
  lift-sol td tm l₁ l = do
    just uc ← pure (td .upwards-closure) where
      _ → backtrack "Goal is not liftable"
    pure $ def uc (l₁ v∷ lit (nat l) v∷ tm v∷ [])

  lifting-loop : (fuel : ℕ) → Tactic-desc goal-name by-hlevel → ℕ → Term → Term → Term → Term → TC ⊤
  lifting-loop zero       td _ _ _ _ _ = backtrack "Lifting loop ran out of fuel"
  lifting-loop (suc fuel) td it solution goal l₁ l₂ =
    let's-hope <|> do
      just l₂′ ← pred-term <$> normalise l₂ where
        nothing → backtrack "Lifting loop reached its end with no success"
      lifting-loop fuel td (suc it) solution goal l₁ l₂′
    where
      let's-hope : TC ⊤
      let's-hope = do
        final-solution ← lift-sol td solution l₁ it
        debug-print "tactic.search" 30
          [ "Lifting loop: Trying " , termErr final-solution , " for level " , termErr l₂ ]
        unify goal final-solution

  get-level-from-struct : Tactic-desc goal-name goal-strat → Struct-proj-desc goal-name goal-strat carrier-name true → Term → TC (Level-data goal-strat)
  get-level-from-struct {goal-strat = none} _ _ _ = pure tt
  get-level-from-struct {goal-name} {goal-strat = by-hlevel} td spd ty = do
    def actual-goal-name args ← reduce ty where
      _ → backtrack [ "Structure type isn't an application of " , nameErr goal-name ]
    guard (actual-goal-name name=? (spd .struct-name))
    argsᵥ ← args-list→args-vec (spd .struct-args-length) args
    lv ← [ (λ n → pure (lit (nat n))) , (λ s → select-arg visible s argsᵥ) ]ᵤ (spd .level-selector)
    normalise lv

  treat-as-structured-type : Tactic-desc goal-name goal-strat → Struct-proj-desc goal-name goal-strat carrier-name goal-nat → Term → TC ⊤
  treat-as-structured-type td spd goal = do
    (wanted-xlevel , ty) ← decompose-goal td goal

    ty ← reduce ty

    def namen args ← pure ty
      where what → backtrack [ "Thing isn't an application, it is " , termErr what ]

    argsᵥ ← args-list→args-vec (spd .projection-args-length) args
    carrier-term ← select-arg visible (spd .carrier-selector) argsᵥ
    go td spd wanted-xlevel carrier-term
    where
      go : ∀{gn gs gin} (td : Tactic-desc gn gs) (spd : Struct-proj-desc gn gs carrier-name gin) → Level-data gs → Term → TC ⊤
      go {gs = by-hlevel} {gin = true} td spd wanted-xlevel carrier-term = do
        debug-print "tactic.search" 10
          [ "Attempting to treat as " , nameErr (spd .struct-name) , " " , termErr wanted-xlevel ]
        actual-level ← infer-type carrier-term >>= get-level-from-struct td spd
        debug-print "tactic.search" 10
          [ "... but it's actually a(n) " , nameErr (spd .struct-name) , " " , termErr actual-level ]
        lv ← normalise wanted-xlevel
        lv′ ← normalise actual-level
        lifting-loop 10000 td 0 (def (spd .goal-projection) (carrier-term v∷ [])) goal lv′ lv
        commitTC
      go td spd _ carrier-term = do -- seems like it is ok
        unify goal (def (spd .goal-projection) (carrier-term v∷ []))
        commitTC


  compose-instance-helper : Tactic-desc goal-name goal-strat → Level-data goal-strat → Term
  compose-instance-helper {goal-strat = none} td _ = def (td .instance-helper) []
  compose-instance-helper {goal-strat = by-hlevel} td lv = def (td .instance-helper) $ unknown h∷ unknown h∷ lv v∷ []

  use-instance-search : Tactic-desc goal-name goal-strat → Bool → Term → TC ⊤
  use-instance-search {goal-name} td has-alts goal = run-speculative do
    (lv , ty) ← decompose-goal td goal
    (mv , solved) ← new-meta′ (compose-instance td lv ty) <|> backtrack []
    instances ← get-instances mv

    t ← quoteTC instances
    debug-print "tactic.search" 10
      [ "Using instance search for\n" , termErr ty
      , "\nFound candidates\n "       , termErr t ]

    let
      go : List Term → TC (⊤ × Bool)
      go = λ where
        (x ∷ []) → do
          unify solved x
          with-reduce-defs (false , td .instance-helper ∷ []) $
            unify goal (compose-instance-helper td lv)
          pure (tt , true)

        [] → if has-alts
          then backtrack "No possible instances, but have other decompositions to try"
          else pure (tt , false)

        _ → backtrack "Too many possible instances; will not use instance search for this goal"
    go instances


  use-projections : Tactic-desc goal-name goal-strat → Term → TC ⊤
  use-projections {goal-name} {goal-strat} td goal = do
    def qn _ ← (snd <$> decompose-goal td goal) >>= reduce
      where tm → backtrack [ "Term " , termErr tm , " is not headed by a definition; ignoring projections." ]

    go-alt ← infer-type goal
    debug-print "tactic.search" 20
      [ "Will attempt to use projections for goal\n" , termErr go-alt ]

    (solved , instances) ← run-speculative do
      goal-strat-term ← quoteTC goal-strat >>= normalise
      (mv , solved) ← new-meta′ (def (quote Struct-proj-desc) (lit (name goal-name) v∷ goal-strat-term v∷ lit (name qn) v∷ unknown v∷ []))
        <|> type-error [ "No projections found for: " , termErr goal ]

      (x ∷ xs) ← get-instances mv
        where [] → pure ((unknown , []) , false)

      pure ((solved , x ∷ xs) , true)

    nondet (eff List) instances λ a → do
      ty ← with-reduce-defs (false , atoms td) (infer-type goal >>= reduce)
      debug-print "tactic.search" 20 $
        "Outer type: " ∷ termErr ty ∷ []
      projection-type ← infer-type a
      def _ (_ ∷ _ ∷ _ ∷ goal-nat-term v∷ []) ← infer-type a where
        _ → type-error "Sorry, this shouldn't have happened"
      goal-nat ← unquoteTC {A = Bool} goal-nat-term
      projection ← unquoteTC {A = Struct-proj-desc goal-name goal-strat qn goal-nat} a
      treat-as-structured-type td projection goal
      unify solved a

  remove-invisible : Term → Term → TC Term
  remove-invisible
    (lam _ (abs _ t))
    (pi (arg (arg-info invisible _) _) (abs _ ret))
    = remove-invisible t ret
  remove-invisible inner _ = pure inner

  wrap-lams : ℕ → Term → Term
  wrap-lams zero r = r
  wrap-lams (suc x) r = lam visible $ abs "a" $ wrap-lams x r

  extend-n : ℕ → TC ((A : Type ℓ) → TC A → TC A)
  extend-n zero = pure λ _ x → x
  extend-n (suc n) = do
    rest ← extend-n n
    lift mv ← rest (Lift _ Term) $ lift <$> new-meta unknown
    let domain = arg (arg-info visible (modality relevant quantity-ω)) mv
    pure λ a k → rest a $ extend-context "a" domain $ k

  search : Tactic-desc goal-name goal-strat → Bool → Level-data goal-strat → (fuel : ℕ) → Term → TC ⊤

  gen-args
    : ℕ                  -- ^ fuel
    → (gs : Goal-strat)  -- ^ simple or indexed
    → Bool               -- ^ Are there any alternatives after this one?
    → Level-data gs      -- ^ What level are we searching for?
    → Term               -- ^ Goal
    → Name               -- ^ Name of the lemma,
    → List (Arg-spec gs) -- ^ and the arguments we should invent.

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
  gen-args 0 _ _ _ _ _ _ _ _ = type-error "gen-args: no fuel"
  gen-args (suc fuel) gs has-alts level goal defn [] accum cont = do
    -- If we have no arguments to generate, then we can go ahead and
    -- use the accumulator as-is.
    unify goal (def defn (List.reverse-fast accum))
    debug-print "tactic.search" 10
      [ "Committed to solution: " , termErr (def defn (List.reverse-fast accum)) ]
    cont

  gen-args (suc fuel) gs has-alts level goal defn (x ∷ args) accum cont with gs | x
  ... | by-hlevel | `level-suc = gen-args fuel by-hlevel has-alts (suc-term level) goal defn args (level v∷ accum) cont
  ... | by-hlevel | `level-minus 0 = gen-args fuel by-hlevel has-alts level goal defn args (level v∷ accum) cont
  ... | by-hlevel | `level-minus n@(suc _) =
    do
      level ← normalise level
      debug-print "tactic.search" 10
        [ "Hint demands offset, performing symbolic monus, subtracting from\n"
        , termErr level ]
      level′ ← monus level n
      gen-args fuel by-hlevel has-alts level goal defn args (level′ v∷ accum) cont
    where
      monus : Term → ℕ → TC Term
      monus (lit (nat n)) k = pure $ lit (nat (n ∸ k))
      monus tm zero = pure tm
      monus thezero@(con (quote zero) []) (suc it) = pure thezero
      monus (con (quote suc) (x v∷ [])) (suc it) = do
        x ← reduce x
        monus x it
      monus tm (suc it) = do
        debug-print "tactic.search" 10 [ "Dunno how to take 1 from " , termErr tm ]
        type-error []

  ... | gs | `term t = gen-args fuel gs has-alts level goal defn args (t v∷ accum) cont

  ... | gs | `search-under under subgoal-name = do
    debug-print "tactic.search" 10 [ "Going under " , termErr (lit (nat under)) ]
    go-under ← extend-n under
    mv ← go-under Term do
      debug-print "tactic.search" 10 "In extended context"
      new-meta unknown
    debug-print "tactic.search" 10 [ "Metavariable: " , termErr (wrap-lams under mv) ]
    gen-args fuel gs has-alts level goal defn args (wrap-lams under mv v∷ accum) do
      cont
      tactic-instance ← do
        solved@(meta mv′ _) ← new-meta (def (quote Tactic-desc) (lit (name subgoal-name) v∷ unknown v∷ []))
          where _ → type-error [ "Could not get tactic instances:" , termErr goal ]
        (ti ∷ []) ← get-instances mv′ where
          [] → type-error [ "No tactic found for the goal " , termErr goal ]
          _  → type-error [ "Multiple tactics for the same goal " , termErr goal ]
        unify solved ti
        pure ti
      def _ (_ ∷ subgoal-strat-term v∷ []) ← infer-type tactic-instance where
        _ → type-error "Sorry, this shouldn't have happened"
      subgoal-strat ← unquoteTC {A = Goal-strat} subgoal-strat-term
      next-td ← unquoteTC {A = Tactic-desc subgoal-name subgoal-strat} tactic-instance
      go-under ⊤ $ search next-td has-alts dummy-level fuel mv


  use-decomp-hints
    : Tactic-desc goal-name goal-strat
    → ℕ
    → Level-data goal-strat × Term
    → Term
    → Term
    → List Term
    → TC (⊤ × Bool)
  use-decomp-hints _ 0 _ _ _ _ = type-error "use-decomp-hints: no fuel"
  use-decomp-hints {goal-name} {goal-strat} td (suc fuel) (lv , goal-ty) goal solved (c₁ ∷ cs) = with-reduce-defs (false , atoms td) do
    ty  ← infer-type c₁
    c₁′ ← reduce c₁
    (remove-invisible c₁′ ty >>= λ where
      (con (quote decomp) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ nm v∷ argspec v∷ [])) → do
        debug-print "tactic.search" 10
          [ "Using " , termErr nm , " decomposition for:\n"
          , termErr (def goal-name $ level-term lv v∷ goal-ty v∷ []) ]

        nm′ ← unquoteTC nm
        argsp ← unquoteTC argspec
        gen-args fuel goal-strat (not (length cs == 0)) lv goal nm′ argsp [] (pure tt)
        no-constraints $ unify solved c₁

        pure (tt , true)

      t → backtrack [ "Non-canonical hint: " , termErr t ])

      <|> use-decomp-hints td fuel (lv , goal-ty) goal solved cs

  use-decomp-hints _ _ (_ , goal-ty) _ _ [] =
    backtrack [ "Ran out of decomposition hints for " , termErr goal-ty ]

  drop-pis : Term → Term
  drop-pis (pi _ (abs _ x)) = drop-pis x
  drop-pis x = x

  use-hints : Tactic-desc goal-name goal-strat → ℕ → Term → TC ⊤
  use-hints _ 0 _ = type-error "use-hints: no fuel"
  use-hints {goal-name} td (suc fuel) goal = run-speculative do
    (lv , ty) ← decompose-goal td goal
    wait-for-principal-arg ty

    (mv , solved) ← new-meta′ (def (quote goal-decomposition) (lit (name goal-name) v∷ ty v∷ []))
    decomp-instances ← get-instances mv

    t ← quoteTC decomp-instances >>= normalise
    debug-print "tactic.search" 10
      [ "Finding decompositions for\n" , termErr ty
      , "\nFound candidates\n "        , termErr t ]

    use-decomp-hints td fuel (lv , ty) goal solved decomp-instances


  search td has-alts _     0          goal = unify goal unknown
  search td has-alts level (suc fuel) goal
    =   use-projections td goal
    <|> use-hints td fuel goal
    <|> use-instance-search td has-alts goal
    <|> type-error "Search failed!"


  decompose-goal-top
    : Tactic-desc goal-name goal-strat → Term → TC (Level-data goal-strat × Term × Telescope)
  decompose-goal-top td goal = do
      ty ← with-reduce-defs (false , atoms td) $
        (infer-type goal >>= reduce) >>= wait-just-a-bit
      go ty
    where
      go : Term → TC _
      go (pi (arg as at) (abs vn cd)) = do
        (lv , inner , delta) ← go cd
        pure $ lv , inner , (vn , (arg as at)) ∷ delta
      go tm = do
        (lv , inner) ← decompose-goal′ td tm
        pure $ lv , inner , []

-- this is the way
search-tactic-worker : Tactic-desc goal-name goal-strat → Term → TC ⊤
search-tactic-worker {goal-name} td goal = do
  ty ← with-reduce-defs (false , atoms td) $ infer-type goal >>= reduce
  debug-print "tactic.search" 10 [ "Target type: " , termErr ty ]
  (lv , ty , delta) ← decompose-goal-top td goal
    <|> type-error
      [ "Goal type is not of the form ‶" , nameErr goal-name , "″:\n"
      , termErr ty ]

  let delta = List.reverse-fast delta
  solved ← enter delta do
    goal′ ← new-meta $ compose-goal td lv ty
    search td false lv 50 goal′
    pure goal′
  unify goal (leave delta solved)
