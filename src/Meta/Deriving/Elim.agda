-- Naïm Favier 2023
{-# OPTIONS --safe #-}
module Meta.Deriving.Elim where

open import Foundations.Prelude

open import Foundations.HLevel public

open import Meta.Append
open import Meta.Effect.Alt
open import Meta.Effect.Traversable
open import Meta.Reflection.Argument
open import Meta.Reflection.Base
open import Meta.Reflection.Neutral
open import Meta.Reflection.Signature
open import Meta.Reflection.Subst

open import Correspondences.Discrete

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Maybe.Base as Maybe
open import Data.Maybe.Instances.Bind
open import Data.Nat.Base
open import Data.List.Base
open import Data.List.Instances.Alt
open import Data.List.Instances.Append
open import Data.List.Instances.Discrete
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom
open import Data.List.Instances.Traversable
open import Data.List.Operations
open import Data.Maybe.Instances.Alt
open import Data.Maybe.Instances.Traversable
open import Data.Reflection
open import Data.String.Instances.Append

{-
A macro for generating induction principles for (higher, indexed) inductive types.

We support inductive types in the form presented in "Pattern Matching Without K"
by Cockx et al, section 3.1, with the addition of higher inductive types.
Reusing the terminology from that paper, the idea is to translate the constructors
of a data type into corresponding *methods* along with spines that tell us how to
apply them to build the eliminator's clauses.

When generating an eliminator into (n-2)-types, we automatically omit the methods that
follow from h-level (i.e. those corresponding to constructors with at least n
nested `Pathᴾ`s).

Due to limitations of the reflection interface, path constructors between composites
are not supported.
-}

Replacements = List (Term × Term)

subst-replacements : Subst → Replacements → Maybe Replacements
subst-replacements s rs = do
  let u = map (bimap (applyS s) (applyS s)) rs
  for u λ where (ma , mb) → ⦇ ma , mb ⦈

instance
  Has-subst-Replacements : Has-subst Replacements
  Has-subst-Replacements = record { applyS = subst-replacements }

record Elim-options : Type where
  field
    -- Whether to generate an induction principle or a recursion principle.
    -- (P : D → Type ℓ) vs (P : Type ℓ)
    induction : Bool

    -- If `just n`, assume the motive has hlevel n and omit methods accordingly.
    into-hlevel : Maybe ℕ

    -- Hide the motive argument in the eliminator's type?
    -- (P : D → Type ℓ) vs. {P : D → Type ℓ}
    hide-motive : Bool

    -- Hide the indices in the motive's type?
    -- (P : (is : Ξ) → D is → Type ℓ) vs. (P : {is : Ξ} → D is → Type ℓ)
    hide-indices : Bool

    -- Hide non-inductive hypotheses in method types?
    -- (Psup : (x : A) (f : B x → W A B) (Pf : ∀ b → P (f b)) → P (sup x f))
    -- vs.
    -- (Psup : {x : A} {f : B x → W A B} (Pf : ∀ b → P (f b)) → P (sup x f))
    -- Arguments hidden in the constructor's type are always hidden.
    hide-cons-args : Bool

private
 module Induction
  (opts : Elim-options)
  (D : Name) (pars : ℕ) (ix-tel : Telescope) (cs : List Name)
  where

  open Elim-options opts

  -- Given a term c : T, produce a replacement c↑ : T↑ (see below).
  -- The Replacements argument maps constructors and variables to their
  -- lifted version.
  replace  : (fuel : ℕ) → Replacements → Term → Maybe Term
  replace* : (fuel : ℕ) → Replacements → Args → Args

  lookupR : Term → Replacements → Maybe Term
  lookupR t [] = nothing
  lookupR t@(con c _) ((con c′ _ , r) ∷ rs) with c name=? c′
  ... | true  = just r
  ... | false = lookupR t rs
  lookupR t@(var i _) ((var i′ _ , r) ∷ rs) with i == i′
  ... | true  = just r
  ... | false = lookupR t rs
  lookupR t (_ ∷ rs) = lookupR t rs

  replace 0 _ _ = nothing
  replace (suc fuel) rs (lam v (abs n t)) = do
    rs′ ← raise 1 rs
    t′  ← replace fuel rs′ t
    pure (lam v (abs n t′))
  replace (suc fuel) rs t@(con c args) = do
    r ← lookupR t rs
    apply-tm* fuel r (replace* fuel rs (drop pars args))
  replace (suc fuel) rs t@(var i args) = do
    r ← lookupR t rs
    apply-tm* fuel r (replace* fuel rs args)
  replace (suc fuel) rs _ = nothing

  replace* 0 _ _ = []
  replace* (suc fuel) rs [] = []
  replace* (suc fuel) rs (arg ai t ∷ as) with replace fuel rs t
  ... | just t′ = hide-if hide-cons-args (arg ai t) ∷ arg ai t′ ∷ replace* fuel rs as
  ... | nothing = arg ai t ∷ replace* fuel rs as

  {-
  The main part of the algorithm: computes the method associated to a constructor.

  In detail, given
    a motive `P : (is : Ξ) → D ps is → Type ℓ`
    a term `c : T = Δ → D ps is`
  produces
    the "lifted" type `T↑ = Δ↑ → P is (c ρ)`
      where `Δ↑ ⊢ ρ : Δ` is an embedding
      where types of the form `S = Φ → D ps is` in Δ are replaced recursively with `{S}, S↑` in Δ↑
      (this only occurs with a recursion depth of 1 due to strict positivity)
    and a spine α such that
      rec : Π P, Δ ⊢ α : Δ↑
      where Π P = (is : Ξ) → (d : D ps is) → P is d
  or nothing if T doesn't end in `D ps`.

  Example: W A B
    sup : (a : A) (f : B a → W A B) → W A B
      f : B a → W A B
      display f = ((b : B a) → P (f b))
                , (_ : Π P, b : B a ⊢ b : B a)
    display sup = ((a : A) {f : B a → W A B} (pf : ∀ b → P (f b)) → P (sup a f))
                , (rec : Π P, a : A, f : B a → W A B ⊢ a, {f}, (λ b → rec (f b)))
  -}

  display
    : (fuel depth : ℕ)
    → (ps : Args) -- D's parameters
    → (P : Term)
    → (rs : Replacements) -- a list of replacements from terms to their lifted version,
                          -- used for correcting path boundaries
    → (rec : Term) -- a variable for explicit recursion
    → (α : Args) -- accumulator for the spine
    → (c : Term) (T : Term)
    → Maybe (Term × Args) -- (T↑ , α)
  display 0 _ _ _ _ _ _ _ _ = nothing
  display (suc fuel) depth ps P rs rec α c (pi (arg ai x) (abs n y)) = do
    ps  ← raise 1 ps
    P   ← raise 1 P
    rs  ← raise 1 rs
    rec ← raise 1 rec
    α   ← raise 1 α
    c   ← raise 1 c
    let base = do
      c ← pure c <#> arg ai (var₀ 0)
      let α = α ∷r hide-if hide-cons-args (arg ai (var₀ 0))
      display fuel depth ps P rs rec α c y <&> first λ y →
        pi (hide-if hide-cons-args (arg ai x)) (abs n y)
    suc depth-1 ← pure depth
      where _ → base
    x′ ← raise 1 x
    just (h , α′) ← pure (display fuel depth-1 ps P rs unknown [] (var₀ 0) x′)
      where _ → base

    ps ← raise 1 ps
    P  ← raise 1 P
    rs ← (var₀ 1 , var₀ 0) ∷_ <$> raise 1 rs
    c ← do
      c′ ← raise 1 c
      apply-tm fuel c′ (arg ai (var₀ 1))
    let h-tel = pi-view-path h
    l ← tel→lam h-tel <$> do
      rec′ ← raise (length h-tel) rec
      apply-tm* fuel rec′ (infer-tel ix-tel ∷r argN (var (length h-tel) α′))
    let α = α <> [ hide-if hide-cons-args (arg ai (var₀ 0)) , argN l ]
    y ← raise 1 y
    display fuel depth ps P rs rec α c y <&> first λ y →
      pi (hide-if hide-cons-args (arg ai x)) (abs n (pi (argN h) (abs ("P" <> n) y)))

  display (suc fuel) depth ps P rs rec α c (def (quote Pathᴾ) (_ h∷ lam v (abs n y) v∷ l v∷ r v∷ [])) = do
    l   ← replace fuel rs l
    r   ← replace fuel rs r
    ps  ← raise 1 ps
    P   ← raise 1 P
    rs  ← raise 1 rs
    rec ← raise 1 rec
    α ← do
      α′ ← raise 1 α
      pure (α′ ∷r argN (var₀ 0))
    c ← do
      c′ ← raise 1 c
      apply-tm fuel c′ (argN (var₀ 0))
    display fuel depth ps P rs rec α c y <&> first λ y →
      it Pathᴾ ##ₕ unknown ##ₙ lam v (abs n y) ##ₙ l ##ₙ r

  display (suc fuel) depth ps P rs rec α c (def D′ args) = do
    true ← pure (D name=? D′)
      where _ → nothing
    let ps′ , is = split-at pars args
    yes _ ← pure (ps ≟ ps′)
      where _ → nothing
    Pc ← apply-tm* fuel P (if induction then hide-if hide-indices is <> c v∷ [] else [])
    pure (Pc , α)
  display (suc fuel) depth ps P rs rec α c _ = nothing

  try-hlevel : Term → TC (Maybe Term)
  try-hlevel T =
    (do
      maybe→alt into-hlevel
      m ← new-meta T
      unify m $ it centre ##ₙ (it hlevel ##ₕ unknown ##ₕ T ##ₙ lit (nat 0))
      pure (just m))
    <|> pure nothing

  ×-map₁₂ : ∀ {A B C : Type} → (A → A) → (B → B) → A × B × C → A × B × C
  ×-map₁₂ f g (a , b , c) = (f a , g b , c)

  -- Loop over D's constructors and build the method telescope, constructor
  -- replacements and spines to apply them to.
  methods : Args → Term → TC (Telescope × List Args × Replacements)
  methods ps P = go full-tank ps P [] cs where
    go : (fuel : ℕ) → Args → Term → Replacements → List Name → TC (Telescope × List Args × Replacements)
    go 0 _ _ _ _ = type-error []
    go (suc fuel) ps P rs [] = pure ([] , [] , rs)
    go (suc fuel) ps P rs (c ∷ cs) = do
      let c′ = con c (hide ps)
      cT ← do
        cT ← get-type c
        cT ← normalise cT
        pi-applyTC cT ps
      just (methodT , α) ← pure (display fuel 1 ps P rs (var₀ 0) [] c′ cT)
        where _ → type-error [ "The type of constructor " , name-err c , " is not supported" ]
      try-hlevel methodT >>= λ where
        (just m) → do
          -- The type of the method is solvable by hlevel (i.e. contractible):
          -- we can omit that type from the telescope and replace the method with
          -- a call to `hlevel 0 .centre`.
          let rs = (c′ , m) ∷ rs
          go fuel ps P rs cs <&> ×-map₁₂ id (α ∷_)
        nothing → do
          -- Otherwise, add m : T to the telescope and replace the corresponding
          -- constructor with m henceforth.
          method ← ("P" <>_) <$> render-name c
          ps  ← raiseTC 1 ps
          P   ← raiseTC 1 P
          rs  ← do
            rs′ ← raiseTC 1 rs
            pure ((c′ , var₀ 0) ∷ rs′)
          extend-context method (argN methodT) (go fuel ps P rs cs) <&>
            ×-map₁₂ ((method , argN methodT) ∷_) (α ∷_)

make-elim-with : Elim-options → Name → Name → TC ⊤
make-elim-with opts elim D = with-normalisation true do
  DT ← get-type D >>= normalise -- D : (ps : Γ) (is : Ξ) → Type _
  data-type pars cs ← get-definition D
    where _ → type-error [ "not a data type: " , name-err D ]
  let
    open Elim-options opts
    DTTel , _ = pi-view DT
    par-tel , ix-tel = split-at pars DTTel
    par-telH = hide par-tel
    ix-tel = hide-if hide-indices ix-tel
    DTel = ix-tel ∷r ("" , argN (def D (tel→args 0 DTTel))) -- (is : Ξ) (_ : D ps is)
  DTel ← raiseTC 1 DTel
  let
    PTel = if induction then id else λ _ → []
    argP = if hide-motive then argH else argN
    motiveTel = ("ℓ" , argH (quoteTerm Level))
              -- P : DTel → Type ℓ
              ∷ ("P" , argP (unpi-view (PTel DTel) (agda-sort (set (var₀ (length (PTel DTel)))))))
              ∷ []
  DTel ← raiseTC 1 DTel
    -- We want to take is-hlevel as an argument, but we need to work in a context
    -- with an H-Level instance in scope.
    -- (d : DTel) → is-of-hlevel n (P d)
  let
    hlevelTel = maybe→alt into-hlevel <&> λ n → "h" , argN
      (unpi-view (PTel DTel)
        (it is-of-hlevel ##ₙ lit (nat n) ##ₙ var (length (PTel DTel)) (tel→args 0 (PTel DTel)) ))
    -- {d : DTel} {k : Nat} → H-Level (n + k) (P d)
    H-LevelTel = maybe→alt into-hlevel <&> λ n → "h" , argI
      (unpi-view (hide (PTel DTel)) (pi (argH (quoteTerm ℕ)) (abs "k"
        (it H-Level ##ₙ (it _+_ ##ₙ lit (nat n) ##ₙ var₀ 0) ##ₙ var (1 + length (PTel DTel)) (tel→args 1 (PTel DTel))))))
    ps = tel→args (length motiveTel + length hlevelTel) par-tel
    P = var₀ (length hlevelTel)
    module I = Induction opts D pars ix-tel cs
  methodTel , αs , rs ← in-context (reverse-fast (par-telH <> motiveTel <> H-LevelTel)) (I.methods ps P)
  let baseTel = par-telH <> motiveTel <> hlevelTel <> methodTel
  DTel ← raiseTC (length hlevelTel + length methodTel) DTel
  P ← raiseTC (length methodTel + length DTel) P
  Pd ← apply*TC P (tel→args 0 (PTel DTel))
  let
    -- ∀ (ps : Γ) {ℓ} {P} (h : ∀ d → is-of-hlevel n (P d)) (ms : methodTel) (d : DTel) → P d
    elimT = unpi-view (baseTel <> DTel) Pd
  elimT′ ← just <$> get-type elim <|> nothing <$ declare-def (argN elim) elimT
  for elimT′ (unify elimT) -- Give a nicer error if the types don't match
  ix-tel ← raiseTC (length motiveTel + length hlevelTel + length methodTel) ix-tel
  ps ← raiseTC (length methodTel + length ix-tel) ps
  rs ← raiseTC (length ix-tel) rs
  -- The replacements are in the H-Level context, so we substitute them back into
  -- our context using basic-instance.
  let h = length methodTel + length ix-tel
  rs ← do
    just n ← pure into-hlevel
      where _ → pure rs
    let f = applyS $ inplaceS h $ tel→lam (hide (PTel DTel))
          $ it hlevel-basic-instance ##ₙ lit (nat n) ##ₙ var (h + length (PTel DTel)) (tel→args 0 (PTel DTel))
    maybe→tc (f rs) []
  clauses ← in-context (reverse-fast (baseTel <> ix-tel)) do
    let get-clause = λ (c , α) → do
      cT ← flip pi-applyTC ps =<< normalise =<< get-type c
      debug-print "tactic.derive.elim" 20 [ "cT = " , term-err cT ]
      let cTel = pi-view-path cT
          pats = tel→pats (length cTel) (baseTel <> ix-tel) ∷r argN (con c (tel→pats 0 cTel))
          rec = def elim (tel→args (length ix-tel + length cTel) baseTel)
      α ← maybe→tc (applyS (singletonS (length cTel) rec) α) []
      just m ← pure (I.replace full-tank rs (con c (hide ps)))
        where _ → type-error []
      m ← flip maybe→tc [] do
        m′ ← raise (length cTel) m
        apply-tm* full-tank m′ α
      pure $ clause (baseTel <> ix-tel <> cTel) pats m
    traverse get-clause (zip cs αs)
  define-function elim clauses

default-elim = record
  { induction = true
  ; into-hlevel = nothing
  ; hide-motive = true
  ; hide-indices = true
  ; hide-cons-args = false
  }

default-elim-visible = record
  { induction = true
  ; into-hlevel = nothing
  ; hide-motive = false
  ; hide-indices = false
  ; hide-cons-args = false
  }

default-rec = record default-elim { induction = false }
default-rec-visible = record default-elim-visible { induction = false }

_into_ : Elim-options → ℕ → Elim-options
opts into n = record opts { into-hlevel = just n }

make-elim make-rec : Name → Name → TC ⊤
make-elim = make-elim-with default-elim
make-rec = make-elim-with default-rec

make-elim-n make-rec-n : ℕ → Name → Name → TC ⊤
make-elim-n n = make-elim-with (default-elim into n)
make-rec-n n = make-elim-with (default-rec into n)
