-- Reed Mullanix 2024
{-# OPTIONS --safe --no-exact-split #-}
module Meta.Copattern where

open import Meta.Prelude
open import Meta.Reflection

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Traversable
open import Data.Reflection.Argument
open import Data.Reflection.Error
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Name
open import Data.Reflection.Term
open import Data.String.Base

--------------------------------------------------------------------------------
-- Macros for manipulating copattern definitions.

-- Make a top-level copattern binding for an existing record.
make-copattern : Bool → Name → Term → Term → TC ⊤
make-copattern declare? def-name tm tp = do
  -- Ensure that codomain is a record type.
  let tele , cod-tp = pi-view tp
  def rec-name params ← pure cod-tp
    where _ → type-error [ "make-copattern: codomain of " , term-err tp , " is not a record type." ]

  inst-tm ← apply*TC tm (tel→args 0 tele)

  -- Construct copattern clauses for each field.
  ctor , fields ← get-record-type rec-name
  clauses ←
    in-context (reverse-fast tele) $
      for fields λ where (arg field-info field-name) → do
      -- Infer the type of the field with all known arguments instantiated.
      field-tp ← infer-type (def field-name [ argN inst-tm ])

      -- Agda will insert implicits when defining copatterns even
      -- with 'withExpandLast true', so we need to do implicit instantiation
      -- by hand. There are also cases where it's better to fully
      -- eta-expand than not (e.g. the 'helper' we're expanding has a
      -- field defined by lazy matching, which does not reduce unless
      -- applied, and would cause duplication of the big input term). So
      -- we fully eta-expand clauses here.
      -- First, we strip off all leading quantifiers from the field
      -- type.
      let field-tele , tp = pi-view field-tp
          nargs = length field-tele
          clause-tele = tele ++ field-tele

      -- Construct the pattern portion of the clause, making sure to bind
      -- all implicit variables. Note that copattern projections are always visible.
      let pat =
            tel→pats nargs tele ++
            arg (set-visibility visible field-info) (proj field-name) ∷
            tel→pats 0 field-tele

      -- Construct the body of the clause, making sure to apply all
      -- arguments bound outside the copattern match, and apply the
      -- eta-expanded arguments. We also need to apply all of the
      -- implicit arguments to 'tm'.
      zz ← raiseTC nargs inst-tm
      body ←
        in-context (reverse clause-tele) $
        reduce (def field-name (argN zz ∷ tel→args 0 field-tele))

      -- Construct the final clause.
      pure $ clause clause-tele pat body

  -- Define a copattern binding, and predeclare its type if required.
  when declare? do
    declare-def (argN def-name) tp <|> pure tt

  -- Construct the final copattern.
  define-function def-name clauses

-- Repack a record type.
-- Will also accept functions into record types like `A → Record`,
-- and will perform a pointwise repacking.
repack-record : Term → Term → TC Term
repack-record tm tp = do
  -- Ensure that codomain is a record type.
  tele , cod-tp ← pi-view <$> reduce tp
  def rec-name params ← pure cod-tp
    where _ → type-error [ "repack-record: codomain of " , term-err tp , " is not a record type." ]

  -- Instantiate the term with all telescope arguments to saturate it.
  inst-tm ← apply*TC tm (tel→args 0 tele)

  -- Construct fields for each projection.
  ctor , fields ← get-record-type rec-name
  args ← in-context (reverse-fast tele) $
    for fields λ where (arg field-info field-name) →
                         argN <$> reduce (def field-name [ argN inst-tm ])

  -- Builld a pointwise repacking.
  pure (tel→lam tele (con ctor args))

-- Helper for the 'define' macros; Unifies the given goal with the type
-- of the given function, if it has been defined. If the function has
-- not been defined, and the first argument is 'false', then an error is
-- raised.
type-for : String → Bool → Name → Term → TC ⊤
type-for tac decl? fun goal = (get-type fun >>= unify goal) <|> do
  unless decl? $ type-error
    [ "define-" , str-err tac , ": the function "
    , name-err fun , " should already have been declared."
    ]


--------------------------------------------------------------------------------
-- Usage

{-
Write the following in a module:
>  unquoteDecl copat = declare-copattern copat thing-to-be-expanded
If you wish to give the binding a type annotation, you can also use
>  copat : Your-type
>  unquoteDecl copat = declare-copattern copat thing-to-be-expanded
All features of non-recursive records are supported, including instance
fields and fields with implicit arguments.
These macros also allow you to lift functions 'A → some-record-type'
into copattern definitions. Note that Agda will generate meta for
implicits before performing quotation, so we need to explicitly
bind all implicits using a lambda before quotation!
-}

declare-copattern : ∀ {ℓ} {A : Type ℓ} → Name → A → TC ⊤
declare-copattern {A = A} nm x = do
  `x ← quoteTC x
  `A ← quoteTC A
  make-copattern true nm `x `A

define-copattern
  : ∀ {ℓ} (nm : Name)
  → {@(tactic (type-for "copattern" true nm)) A : Type ℓ}
  → A → TC ⊤
define-copattern nm {A} x = do
  `A ← quoteTC A
  `x ← define-abbrev nm "value" `A =<< quoteTC x
  make-copattern false nm `x `A

{-
There is a slight caveat with level-polymorphic defintions, as
they cannot be quoted into any `Type ℓ`. With this in mind,
we also provide a pair of macros that work over `Typeω` instead.
-}

declare-copatternω : ∀ {U : Typeω} → Name → U → TC ⊤
declare-copatternω nm A = do
  `A ← quoteωTC A
  -- Cannot quote things in type Typeω, but we can infer their type.
  `U ← infer-type `A
  make-copattern true nm `A `U

define-copatternω
  : (nm : Name) {@(tactic (type-for "copatternω" false nm)) U : Typeω}
  → U → TC ⊤
define-copatternω nm A = do
  `U ← get-type nm
  `A ← define-abbrev nm "vlaue" `U =<< quoteωTC A
  make-copattern false nm `A `U

{-
Another common pattern is that two records `r : R p` and `s : R q` may contain
the same data, but they are parameterized by different values.
The `define-eta-expansion` macro will automatically construct a function
`R p → R q` that eta-expands the first record out into a copattern definition.
-}

define-eta-expansion : Name → TC ⊤
define-eta-expansion nm = do
  tp ← reduce =<< infer-type (def₀ nm)
  let tele , _ = pi-view tp
  let tm = tel→lam tele (var₀ 0)
  make-copattern false nm tm tp

--------------------------------------------------------------------------------
-- Tests

private module Test where
  -- Record type that uses all interesting features.
  record Record {ℓ} (A : Type ℓ) : Type ℓ where
    no-eta-equality
    constructor mk
    field
      ⦃ c ⦄ : A
      { f } : A → A
      const′ : ∀ {x} → f x ＝ c

  -- Record created via a constructor.
  via-ctor : Record ℕ
  via-ctor = mk ⦃ c = 0 ⦄ {f = λ _ → 0} refl

  -- Both macros work.
  unquoteDecl copat-decl-via-ctor = declare-copattern copat-decl-via-ctor via-ctor

  copat-def-via-ctor : Record ℕ
  unquoteDef copat-def-via-ctor = define-copattern copat-def-via-ctor via-ctor

  -- Record created by a function.
  module _ (r : Record ℕ) where
    open Record r
    via-function : Record ℕ
    via-function .c = suc c
    via-function .f = suc ∘ f
    via-function .const′ = ap suc const′

  -- Also works when applied to the result of a function.
  unquoteDecl copat-decl-via-function = declare-copattern copat-decl-via-function (via-function via-ctor)

  -- Test to see how we handle unused parameters.
  record Unused (n : ℕ) : Type where
    field actual : ℕ

  zero-unused-param : Unused 0
  zero-unused-param = record { actual = 0 }

  one-unused-param : ∀ {n} → Unused n
  unquoteDef one-unused-param = declare-copattern one-unused-param zero-unused-param
  -- This is a type error:
  -- unquoteDef one-unused-param = define-copattern one-unused-param zero-unused-param
  -- because the 'define' macro propagates the type of the thing being
  -- defined inwards.

  -- Functions into records that are universe polymorphic
  neat : ∀ {ℓ} {A : Type ℓ} → A → Record A
  neat a .Record.c = a
  neat a .Record.f _ = a
  neat a .Record.const′ = refl

  -- Implicit insertion is correct for the define- macro, since the type
  -- of the function is given.
  cool : ∀ {ℓ} {A : Type ℓ} → A → Record A
  unquoteDef cool = define-copatternω cool neat

  -- Eta-expanders
  expander : ∀ {m n : ℕ} → Unused m → Unused n
  unquoteDef expander = define-eta-expansion expander

  -- Raises a type error: the function should have a declaration.
  -- unquoteDecl uncool = define-copatternω uncool neat
