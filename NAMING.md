NAMING
======

This file provides a guide for how to name things. Note that almost all
files in the library currently follow these guidelines.

For naming conventions specific to the Algebra subfolder, see
[Algebra/NAMING.md](https://github.com/cmcmA20/cubical-mini/blob/master/src/Algebra/NAMING.md).

* Use either descriptive names for universe levels or
  ```
  ℓ ℓ′ ℓ″ ℓ‴ ...
  ```

* Prefer good visually evocative notations to textual names when defining stuff
  (e.g. McBride's unicode calligraphy).

* Names of types should begin with an uppercase letter; names of
  non-type terms should begin with a lowercase letter. The exception
  is types that represent properties, which should begin with `is`
  (for example `is-prop`).

* Use abbreviations to avoid very long names, e.g.
  - `id-l`/`id-r` = identity on the left/right
  - `comm` = commutative
  - `assoc` = associative
  - `idem` = idempotent
  - `absorp` = absorptive
  - `dist-l`/`dist-r` = distribute left/right
  - `comp` = composition
  - `fun` = function
  - `Cat` = category
  - `hom` = homomorphism

* Use kebab-case instead of camelCase, also for properties/lemmas
  related to operations. For example: `+-assoc`, `·-dist-right-+`.

  Builtins and primitives can be left camelCase though.

* Avoid referring to variable names in the names of definitions.
  For example, prefer `+-comm` to something like `m+n≡n+m`.

* Numerical superscripts must be used only for arity specification.

  Numerical subscripts should be preferred to indicate hlevel, but
  can be used for other purposes if it improves readability.

* Use `equiv` or `≃` to refer to equivalences of types or structures.
  Operators can use subscript `ₑ`.

* Use `iso` or `≅` to refer to isomorphisms of types or structures.
  Here an isomorphism is a function with a quasi-inverse, i.e. a
  quasi-equivalence in the sense of the HoTT Book.
  Operators can use subscript `ᵢ`.

* Use `Path` or `＝` to refer to paths in names, not `Eq`, `Id`, or
  other "equality" or "identity"-related names.

* Use `≡` to refer to congruences or some other strict similarity relations.
  When defining a new target language, locally rename `＝` to `≡` for
  definitional equalities of the target language.
  Builtin Agda equality is called `_＝ⁱ_`.

* Prefer using `→` over `to`.

* Results about `PathP` (path overs) should end with `P` (like
  `compP`).

* Type families valued in propositions, either defined as records,
  functions or as truncated inductive types, should start with the word
  `is`: `is-prop`, `is-set`, etc. Predicates should be written _after_
  what they apply to: `Nat-is-set`, `is-prop-is-prop`,
  `is-of-hlevel-is-prop`. Record fields indicating the truth of a predicate
  should be prefixed `has-is-`, since Agda doesn't allow you to shadow
  globals with record fields.

* When defining eliminators, recursors and similar functions for datatypes,
  use the names `elim` and `rec`, potentially with a suitable suffix (like `elim-prop`).
  Do not use `ind`.
  You can look
  [here](https://github.com/cmcmA20/cubical-mini/blob/master/src/Truncation/Propositional/Base.agda)
  to see how diffrent versions of `elim` and `rec` are named and typed.

* The `elim` and `rec` should be used as much as possible without
  renaming, but by importing and renaming the module.
  For instance use `open import Data.Empty as ⊥`
  then use `⊥.rec` or `⊥.elim` rather than doing
  `renaming (rec to rec-⊥)` and using `rec-⊥`.

  Some conventional naming :
  - Empty                   -> ⊥
  - PropositionalTruncation -> PT
  - SetTruncation           -> ST
  - SetQuotient             -> SQ
