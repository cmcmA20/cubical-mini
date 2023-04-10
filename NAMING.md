NAMING
======

This file provides a guide for how to name things. Note that many
files in the library do not currently follow these guidelines.

For naming conventions specific to the Algebra subfolder, see
[Algebra/NAMING.md](https://github.com/agda/cubical/blob/master/Cubical/Algebra/NAMING.md).

* Use either descriptive names for universe levels or
  ```
  ℓ ℓ′ ℓ' ℓ″ ℓ'' ℓ‴ ℓ''' ...
  ```

* Prefer good visually evocative notations when defining stuff (e.g. McBride's
  unicode calligraphy) to textual names.

* Names of types should begin with an uppercase letter; names of
  non-type terms should begin with a lowercase letter. The exception
  is types that represent properties, which should begin with `is`
  (for example `is-prop`).

* Use abbreviations to avoid very long names, e.g.
  - `comm` = commutative
  - `assoc` = associative
  - `dist-right`/`dist-left` = distribute right/left

* Use kebab-case instead of camelCase, also for properties/lemmas
  related to operations. For example: `+-assoc`, `·-dist-right-+`.

* Avoid referring to variable names in the names of definitions.
  For example, prefer `+-comm` to something like `m+n≡n+m`.

* Use Equiv or `≃` to refer to equivalences of types or structures.
  Keep in mind that builtin equivalence definition is called `≃′`.

* Use Iso or `≅` to refer to isomorphisms of types or structures.
  Here an isomorphism is a function with a quasi-inverse, i.e. a
  quasi-equivalence in the sense of the HoTT Book.

* Use `Path` or `＝` to refer to paths in names, not `Eq`, `Id`, or
  other "equality" or "identity"-related names.

* Use `≡` to refer to congruences or some other strict similarity relations.
  When defining a new target language, locally rename `＝` to `≡`.

* Results about `PathP` (path overs) should end with `P` (like
  `compPathP`).

* The order of terms in names should reflect the type and things
  should appear in the order they appear in the type (like
  `is-contr-unit`). For functions things can either be separated by `→`
  (like `is-prop→is-set`) or `to` (like `iso-to-equiv`).

* When defining eliminators, recursors and similar functions for datatypes,
  use the names `elim` and `rec`, potentially with a suitable suffix (like `elim-prop`).
  Do not use `ind`.
  You can look
  [here](https://github.com/agda/cubical/blob/master/Cubical/HITs/SetQuotients/Properties.agda#L42-L92)
  and
  [here](https://github.com/agda/cubical/blob/master/Cubical/HITs/S1/Properties.agda#L14-L20)
  to see how diffrent versions of `elim` and `rec` are named and typed.

* The `elim` and `rec` should be used as much as possible without
  renaming, but by importing and renaming the module.
  For instance use `open import Cubical.Data.Empty as ⊥`
  then use `⊥.rec` or `⊥.elim` rather than doing
  `renaming (rec to rec-⊥)` and using `rec-⊥`.

  Some convetional naming :
  - Empty                   -> ⊥
  - PropositionalTruncation -> PT
  - SetTruncation           -> ST
  - SetQuotient             -> SQ
