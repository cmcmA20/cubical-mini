{-# OPTIONS --safe #-}
-- -vtactic.search:20 -vtc.def:10
module Meta.Search.Base where

open import Foundations.Base

open import Meta.Foldable
open import Meta.Reflection

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Instances.Foldable
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom
open import Data.Maybe.Base
open import Data.Nat.Base

data Arg-spec : Type where
  `level-minus  : (n : ℕ) → Arg-spec
  `search-under : (n : ℕ) (subgoal : Name) → Arg-spec
  `meta         : Arg-spec

pattern `search sg  = `search-under 0 sg
pattern `level-same = `level-minus 0

data goal-decomposition {ℓ} (goal : Name) (T : Type ℓ) : Type where
  decomp : (search-lemma : Name) (arguments : List Arg-spec)
         → goal-decomposition goal T


record Tactic-desc (goal-name : Name) : Type where
  field
    other-atoms              : List Name
    instance-fallback-helper : Name
    upwards-closure          : Maybe Name
    -- ^ it should have a following signature
    --   (h₀ h₁ : HLevel) → whatever h₀ A → whatever (h₁ + h₀) A

  atoms : List Name
  atoms = goal-name ∷ other-atoms


record Struct-proj-desc (goal-name : Name) (carrier-name : Name) : Type where
  field
    struct-name  : Name
    project-goal : Name
    get-level    : Term → TC Term -- TODO refactor this
    get-argument : List (Arg Term) → TC Term

private variable
  ℓ : Level
  A : Type ℓ
  goal-name carrier-name : Name
  n : HLevel

backtrack : List ErrorPart → TC A
backtrack note = do
  debugPrint "tactic.search" 10 $ "Backtracking search... " ∷ note
  typeError $ "Search hit a dead-end: " ∷ note

private
  decompose-goal′ : Tactic-desc goal-name → Term → TC (Term × Term)
  decompose-goal′ {goal-name} td ty = do
    def actual-goal-name (_ ∷ lv v∷ ty v∷ []) ← pure ty where
      _ → backtrack [ "Goal type isn't " , nameErr goal-name ]
    guard (actual-goal-name name=? goal-name)
    ty ← wait-just-a-bit ty
    lv ← wait-just-a-bit lv
    pure (lv , ty)

  decompose-goal : Tactic-desc goal-name → Term → TC (Term × Term)
  decompose-goal td goal = do
    let open Tactic-desc td
    ty ← withReduceDefs (false , atoms) $ inferType goal >>= reduce
    decompose-goal′ td ty

  lift-sol : Tactic-desc goal-name → Term → Term → ℕ → TC Term
  lift-sol td tm _ 0  = pure tm
  lift-sol td tm l₁ l = do
    let module tac = Tactic-desc td
    just uc ← pure tac.upwards-closure where
      nothing → backtrack "Goal is not liftable"
    pure $ def uc (l₁ v∷ lit (nat l) v∷ tm v∷ [])

  pred-term : Term → Maybe Term
  pred-term (con (quote suc) (x v∷ [])) = just x
  pred-term (lit (nat n)) with n
  ... | suc k = just (lit (nat k))
  ... | _ = nothing
  pred-term _ = nothing

  lifting-loop : (fuel : ℕ) → Tactic-desc goal-name → ℕ → Term → Term → Term → Term → TC ⊤
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
        debugPrint "tactic.search" 30
          [ "Lifting loop: Trying " , termErr final-solution , " for level " , termErr l₂ ]
        unify goal final-solution

  treat-as-structured-type : Tactic-desc goal-name → Struct-proj-desc goal-name carrier-name → Term → TC ⊤
  treat-as-structured-type td spd goal = do
    let module proj = Struct-proj-desc spd
    (wanted-level , ty) ← decompose-goal td goal
    debugPrint "tactic.search" 10
      [ "Attempting to treat as " , nameErr proj.struct-name , " " , termErr wanted-level , ": " , termErr ty ]
    ty ← reduce ty

    def namen args ← returnTC ty
      where what → backtrack [ "Thing isn't an application, it is " , termErr what ]

    it ← proj.get-argument args
    actual-level ← inferType it >>= proj.get-level
    debugPrint "tactic.search" 10
      [ "... but it's actually a(n) " , nameErr proj.struct-name , " " , termErr actual-level ]

    lv ← normalise wanted-level
    lv′ ← normalise actual-level
    lifting-loop 10000 td 0 (def (proj.project-goal) (it v∷ [])) goal lv′ lv

    commitTC


  use-instance-search : Tactic-desc goal-name → Bool → Term → TC ⊤
  use-instance-search {goal-name} td has-alts goal = runSpeculative do
    (lv , ty) ← decompose-goal td goal
    solved@(meta mv _) ←
      new-meta (def goal-name (lv v∷ ty v∷ [])) where _ → backtrack []
    instances ← getInstances mv

    t ← quoteTC instances
    debugPrint "tactic.search" 10
      [ "Using instance search for\n" , termErr ty
      , "\nFound candidates\n "       , termErr t ]

    let
      module tac = Tactic-desc td
      go : List Term → TC (⊤ × Bool)
      go = λ where
        (x ∷ []) → do
          unify solved x
          withReduceDefs (false , tac.instance-fallback-helper ∷ []) $ withReconstructed true $
            unify goal (def tac.instance-fallback-helper (lv v∷ []))
          pure (tt , true)

        [] → if has-alts
          then backtrack "No possible instances, but have other decompositions to try"
          else pure (tt , false)

        _ → backtrack "Too many possible instances; will not use instance search for this goal"
    go instances


  search : Tactic-desc goal-name → Bool → Term → ℕ → Term → TC ⊤
  search             td has-alts _     zero    goal = unify goal unknown
  search {goal-name} td has-alts level (suc n) goal
    =   use-projections
    <|> use-hints
    <|> use-instance-search td has-alts goal
    <|> typeError "Search failed!"
    where
      module tac = Tactic-desc td
      use-projections : TC ⊤
      use-projections = do
        def qn _ ← (snd <$> decompose-goal td goal) >>= reduce
          where _ → backtrack "Term is not headed by a definition; ignoring projections."

        go-alt ← inferType goal
        debugPrint "tactic.search" 20
          [ "Will attempt to use projections for goal\n" , termErr go-alt ]

        (solved , instances) ← runSpeculative do
          solved@(meta mv _) ← new-meta (def (quote Struct-proj-desc) (lit (name goal-name) v∷ lit (name qn) v∷ []))
            where _ → typeError [ "No projections found: " , termErr goal ] -- FIXME error message is too vague

          (x ∷ xs) ← getInstances mv
            where [] → pure ((unknown , []) , false)

          pure ((solved , x ∷ xs) , true)

        nondet (eff List) instances λ a → do
          projection ← unquoteTC {A = Struct-proj-desc goal-name qn} a
          ty ← withReduceDefs (false , tac.atoms) (inferType goal >>= reduce)
          debugPrint "tactic.hlevel" 20 $
            "Outer type: " ∷ termErr ty ∷ []
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
        pure λ a k → rest a $ extendContext "a" domain $ k

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
        debugPrint "tactic.search" 10
          [ "Committed to solution: " , termErr (def defn (reverse accum)) ]
        cont

      gen-args has-alts level defn (x ∷ args) accum cont with x
      ... | `level-minus 0 = gen-args has-alts level defn args (level v∷ accum) cont
      ... | `level-minus n@(suc _) =
        do
          level ← normalise level
          debugPrint "tactic.hlevel" 10
            [ "Hint demands offset, performing symbolic monus, subtracting from\n"
            , termErr level ]
          level′ ← monus level n
          gen-args has-alts level defn args (level′ v∷ accum) cont
        where
          monus : Term → ℕ → TC Term
          monus (lit (nat n)) k = pure $ lit (nat (n - k))
          monus tm zero = pure tm
          monus thezero@(con (quote zero) []) (suc it) = pure thezero
          monus (con (quote suc) (x v∷ [])) (suc it) = do
            x ← reduce x
            monus x it
          monus tm (suc it) = do
            debugPrint "tactic.search" 10 [ "Dunno how to take 1 from " , termErr tm ]
            typeError []

      ... | `meta = gen-args has-alts level defn args (unknown v∷ accum) cont

      ... | `search-under under subgoal-name = do
        debugPrint "tactic.search" 10 [ "Going under " , termErr (lit (nat under)) ]
        go-under ← extend-n under
        mv ← go-under Term do
          debugPrint "tactic.search" 10 "In extended context"
          new-meta unknown
        debugPrint "tactic.search" 10 [ "Metavariable: " , termErr (wrap-lams under mv) ]
        gen-args has-alts level defn args (wrap-lams under mv v∷ accum) do
          cont
          tactic-instance ← do
            solved@(meta mv′ _) ← new-meta (def (quote Tactic-desc) (lit (name subgoal-name) v∷ []))
              where _ → typeError [ "Could not get instances:" , termErr goal ]
            (ti ∷ []) ← getInstances mv′ where
              _ → typeError [ "Too few (or many) tactic instances:" , termErr goal ]
            unify solved ti
            pure ti
          next-td ← unquoteTC {A = Tactic-desc subgoal-name} tactic-instance
          go-under ⊤ $ search next-td has-alts unknown n mv

      use-decomp-hints : Term × Term → Term → List Term → TC (⊤ × Bool)
      use-decomp-hints (lv , goal-ty) solved (c₁ ∷ cs) = do
        ty  ← inferType c₁
        c₁′ ← reduce c₁
        (remove-invisible c₁′ ty >>= λ where
          (con (quote decomp) (_ ∷ _ ∷ _ ∷ nm v∷ argspec v∷ [])) → do
            debugPrint "tactic.search" 10
              [ "Using " , termErr nm , " decomposition for:\n"
              , termErr (def goal-name (lv v∷ goal-ty v∷ [])) ]

            nm′ ← unquoteTC nm
            argsp ← unquoteTC argspec
            gen-args (not (length cs == 0)) lv nm′ argsp [] (returnTC tt)
            unify solved c₁

            pure (tt , true)

          t → backtrack [ "Non-canonical hint: " , termErr t ])

          <|> use-decomp-hints (lv , goal-ty) solved cs

      use-decomp-hints (_ , goal-ty) _ [] =
        backtrack [ "Ran out of decomposition hints for " , termErr goal-ty ]

      use-hints : TC ⊤
      use-hints = runSpeculative do
        (lv , ty) ← decompose-goal td goal
        pure ty >>= λ where
          (meta m _) → do
            debugPrint "tactic.search" 10
              "Type under goal is metavariable, blocking to avoid infinite loop"
            blockOnMeta m
          _ → pure tt

        solved@(meta mv _) ← new-meta (def (quote goal-decomposition) (lit (name goal-name) v∷ ty v∷ []))
          where _ → typeError [ termErr ty ]
        instances ← getInstances mv

        t ← quoteTC instances
        debugPrint "tactic.search" 10
          [ "Finding decompositions for\n" , termErr ty
          , "\nFound candidates\n "        , termErr t ]

        use-decomp-hints (lv , ty) solved instances


  decompose-goal-top
    : Tactic-desc goal-name → Term → TC (Term × Term × Telescope)
  decompose-goal-top td goal = do
      let module tac = Tactic-desc td
      ty ← withReduceDefs (false , tac.atoms) $
        (inferType goal >>= reduce) >>= wait-just-a-bit
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
search-tactic-worker : Tactic-desc goal-name → Term → TC ⊤
search-tactic-worker {goal-name} td goal = do
  let module tac = Tactic-desc td
  ty ← withReduceDefs (false , tac.atoms) $ inferType goal >>= reduce
  debugPrint "tactic.search" 10 [ "Target type: " , termErr ty ]
  (lv , ty , delta) ← decompose-goal-top td goal
    <|> typeError
      [ "Goal type is not of the form ‶" , nameErr goal-name , "″:\n"
      , termErr ty ]

  let delta = reverse-fast delta
  solved ← enter delta do
    goal′ ← new-meta (def goal-name (unknown h∷ lv v∷ ty v∷ []))
    search td false lv 15 goal′
    pure goal′
  unify goal (leave delta solved)
  where
    leave : Telescope → Term → Term
    leave [] = id
    leave ((na , arg as _) ∷ xs) = leave xs ∘ lam (arg-vis as) ∘ abs na
    enter : Telescope → TC A → TC A
    enter [] = id
    enter ((na , ar) ∷ xs) = enter xs ∘ extendContext na ar
