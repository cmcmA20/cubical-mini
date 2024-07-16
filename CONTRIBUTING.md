# CONTRIBUTING

- [General terms](#general-terms)
- [Requirements](#requirements)
  - [1 Design](#1-design)
  - [2 Technical](#2-technical)
  - [3 Style](#3-style)
    - [3.1 Format](#31-format)
    - [3.2 Naming](#32-naming)

## General terms

Before submitting changes, make sure they do not contradict the
requirements described in this document.

If your change conflicts with a requirement with the word "MUST", it
will be rejected.

If your change conflicts with a requirement with the word "SHOULD",
it may be accepted if the requirement cannot be met for a valid reason.

Self-check changes against requirements before submitting them, this
will save a lot of time and effort for the maintainer to check them and
increase the likelihood and speed of change acceptance.

The meanings of the terms "MUST" (also "SHOULD", "MAY", etc.) in this document
are in accordance with [RFC 2119](https://datatracker.ietf.org/doc/html/rfc2119).

## Requirements

### 1 Design

- 1.1 Prelude modules **SHOULD** be imported as follows:

  -  `Foundations.Base` when working on other `Foundations.*`
  -  `Foundations.Prelude` when working on `Meta.*` internals
  -  `Meta.Prelude` when working on other modules
  -  `Prelude`, `Algebra.Prelude`, `Categories.Prelude` when using cubical-mini
     as an external dependency

- 1.2 Inductive `Data.*` types **MUST** have:

  -  recursor (`rec`)
  -  dependent eliminator (`elim`)
  -  universal property for mapping out (`universal`)

- 1.3 All `Data.*` types **MUST** have:

  -  path space characterization (`module Path`) + `Extensionality` instance
  -  discreteness instance (if applicable)
  -  strongest finiteness instance (if applicable)

- 1.4 Definitions **SHOULD** be maximally universe polymorphic.

- 1.5 Imports **MUST NOT** be `public` except for modules intended for
  collection and re-export.

- 1.6 Primitives and built-ins **MUST NOT** be imported anywhere except in
  `Foundations.*`, `Data.*.Base`, `IO.*`.

- 1.7 `Base` submodule **MUST** import only the `Foundations.*` modules and
  those essential for the definition.

- 1.8 Definitions **SHOULD** be grouped in folders and modules by math area
  and its' customs, and not by implementation details.

  > `HITs` module would be an example of how NOT to group things as HITs per se
  > aren't studied in this library, they are used as a tool to describe other
  > mathematical concepts.

### 2 Technical

- 2.1 The project **SHOULD** be tested with `make test` before submitting changes.

- 2.2 If macros are used, the `private variable` **SHOULD NOT** be used to
  quantify universe levels, but **SHOULD** be used otherwise.

- 2.3 Option `--safe` **SHOULD** be used.

- 2.4 Options `--no-exact-split`, `--lossy-unification` **MAY** be used.

- 2.5 Record terms **SHOULD** be created using copattern-matching for efficiency.

- 2.6 If function argument can always be inferred, it **MUST** be made implicit.

- 2.7 If function argument is rarely inferred, it **SHOULD** be made explicit.

### 3 Style

#### 3.1 Format

- 3.1.1 Lines **SHOULD** be less than 100 characters in length.

- 3.1.2 The reference to the paper on which the code is based **SHOULD** be at
  the top of the file.

- 3.1.3 Local definitions **MUST** be in `where`, `let-in` or `private`.

  > So that it is easy to see which are the main results of a file
  > and which are just helper definitions.

- 3.1.6 Imports **SHOULD** be grouped in the following order:

  - `Foundations`,
  - `Meta`,
  - `Structures`,
  - `Correspondences`,
  - `Data`,
  - `Functions`.

  And in lexicographical order inside groups.

#### 3.2 Naming

- 3.2.1 Type names **SHOULD** start with a capital letter, except for types
  representing properties, they **MUST** start with `is` (e.g. `is-prop`).

- 3.2.2 Other identifier names **SHOULD** be in kebab case.

- 3.2.3 Numerical superscripts **SHOULD** be used only for arity specification.

- 3.2.4 Numerical subscripts **SHOULD** be used to indicate hlevel.

- 3.2.6 Definition names **MUST NOT** refer to variable names.

  > For example, prefer `+-comm` to something like `m+n≡n+m`.

- 3.2.7 Identifier names **MUST NOT** contain `＝`, use `=` instead.

  > Otherwise it garbles column alignment.

- 3.2.8 Results about `Pathᴾ` (path overs) **SHOULD** end with
  superscript `ᴾ`.

- 3.2.9 Results about displayed stuff **SHOULD** end with superscript `ᴰ`.

- 3.2.10 Predicate names **MUST** be written as suffixes, e.g.:

  - `Nat-is-set`,
  - `is-prop-is-prop`,
  - `is-of-hlevel-is-prop`.

- 3.2.11 Fields of a record indicating the truth of a predicate **MUST** be
  prefixed with `has-`.

- 3.2.12 All long names **SHOULD** be abbreviated, as in the table:

  | Long name             | Abbreviation |
  | ----------------------| ------------ |
  | identity on the left  | `id-l`       |
  | identity on the right | `id-r`       |
  | commutative           | `comm`       |
  | associative           | `assoc`      |
  | idempotent            | `idem`       |
  | absorptive            | `absorp`     |
  | distribute left       | `dist-l`     |
  | distribute right      | `dist-r`     |
  | composition           | `comp`       |
  | function              | `fun`        |
  | category              | `Cat`        |
  | homomorphism          | `hom`        |

- 3.2.13 Level names **MUST** be descriptive or

  ```
  ℓ  ℓ′ ℓ″ ...
  ℓᵃ ℓᵇ ℓᶜ ...
  ℓa ℓb ℓc ...
  ```

- 3.2.14 `≡` **SHOULD** refer to congruences or some other strict similarity
  relations.

  > When defining a new target language, locally rename `＝`
  > to `≡` for definitional equalities of the target language if you
  > need so. Builtin Agda equality is called `_＝ⁱ_`.

- 3.2.15 `→` **SHOULD** be used over `to`.

- 3.2.16 `equiv` or `≃` **SHOULD** refer to equivalences of types or
  structures.

  > Operators can use subscript `ₑ`.

- 3.2.17 `iso` or `≅` **SHOULD** refer to isomorphisms of types or
  structures.

  > Here an isomorphism is a function with a quasi-inverse,
  > i.e. a quasi-equivalence in the sense of the HoTT Book. Operators
  > can use subscript `ᵢ`.

- 3.2.18 `Path` or `=` **SHOULD** refer to paths in names, not `Eq`, `Id`,
  or other "equality" or "identity"-related names.

  > Operators can use subscript `ₚ`.

- 3.2.19 Partial function names (returning `Maybe`) **SHOULD** end with `ᵐ`.
