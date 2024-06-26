# CONTRIBUTING

- [General terms](#general-terms)
- [Requirements](#requirements)
  - [1 Design](#1-design)
  - [2 Technical](#2-technical)
  - [3 Style](#3-style)
    - [3.1 Format](#31-format)
    - [3.2 Textual](#32-textual)
    - [3.3 Naming](#33-naming)

## General terms

This document describes the requirements for the project.

Before submitting changes, make sure that they do not contradict the
requirements described in this document.

If your change conflicts with a requirement with the word "MUST", it
will be rejected.

If your change conflicts with a requirement with the word "SHOULD",
it may be accepted if the requirement cannot be met for a valid reason.

Self-check changes against requirements before submitting them, this
will save a lot of time and effort for the maintainer to check them and
increase the likelihood and speed of change acceptance.

The meanings of the terms "MUST" and "SHOULD" in this document are in
accordance with [RFC 2119](https://datatracker.ietf.org/doc/html/rfc2119).

## Requirements

### 1 Design

- 1.1 All records **MUST** use copattern-matching when created.

  > For efficiency, use pattern matching when instantiating records.
  > This seems especially important when building `Iso`.

- 1.2 All data types **MUST** have:

  -  a recursor (`rec`),
  -  a dependent eliminator (`elim`),
  -  a universal property for outward mapping (`universal`),
  -  a path space characterization (`module Path`),
  -  and useful instances.

- 1.3 All definitions **SHOULD** be universe polymorphic.

- 1.4 All imports **MUST NOT** be `public` except for modules intended for
  collection and re-export.

- 1.5 All primitives or built-ins **MUST NOT** be imported anywhere except in
  `Foundations.*` and `Data.*.Base`.

- 1.6 The `Base` submodule **SHOULD** import only the `Foundations` module and
  those needed only for this definition.

### 2 Technical

- 2.1 The project **MUST** be tested with `make test` before submitting changes.

- 2.2 If macros are used, the `private variable` **SHOULD NOT** be used to
  quantify universe levels, but **SHOULD** be used otherwise.

- 2.3 All files **SHOULD** start with `{-# OPTIONS --safe #-}`.

### 3 Style

#### 3.1 Format

- 3.1.1 All lines **MUST** be less than 100 characters in length.

- 3.1.2 The reference to the paper on which the code is based **SHOULD** be at
  the top of the file.

- 3.1.3 All local definitions **SHOULD** be in `where`, `let-in` or `private`.

  > So that it is easy to see which are the main results of a file
  > and which are just helper definitions.

- 3.1.4 All arguments that can be made implicit without loss **SHOULD** be implicit.

- 3.1.5 All imports **SHOULD** be grouped in the following order:

  - `Foundations`,
  - `Meta`,
  - `Structures`,
  - `Correspondences`,
  - `Data`,
  - `Functions`.

  And in lexicographical order inside groups.

#### 3.2 Textual

- 3.2.1 All names **SHOULD** be in the kebab case.

- 3.2.2 All numerical superscripts **MUST** be used only for arity specification.

- 3.2.3 All numerical subscripts **SHOULD** be used to indicate hlevel.

- 3.2.4 The structure and all names of the modules **SHOULD** reprsent the
  mathematical concept, not the syntax of the agda.

- 3.2.5 All definition names **MUST NOT** refer to variable names.

  > For example, prefer `+-comm` to something like `m+n≡n+m`.

- 3.2.6 All identifier names **SHOULD NOT** contain `＝`.

  > It garbles column alignment.

- 3.2.7 All results about `Pathᴾ` (path overs) **SHOULD** end with
  superscript `ᴾ`.

- 3.2.8 All results about displayed stuff **SHOULD** end with superscript `ᴰ`.

- 3.2.9 All predicate names **MUST** be written as suffixes, e.g.:

  - `Nat-is-set`,
  - `is-prop-is-prop`,
  - `is-of-hlevel-is-prop`.

- 3.2.10 All fields of a record indicating the truth of a predicate **MUST** be
  prefixed with `has-`.

- 3.2.11 All type names **SHOULD** start with a capital letter, except for types
  representing properties, they **MUST** start with `is` (e.g. `is-prop`).

- 3.2.12 All names of non-typical terms **SHOULD** begin with a lowercase letter

- 3.2.13 All long names **SHOULD** be abbreviated, as in the table:

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

#### 3.3 Naming

- 3.3.1 All universe levels names **MUST** be descriptive or

  ```
  ℓ ℓ′ ℓ″ ℓ‴ ...
  ```

- 3.3.2 The `≡` **SHOULD** refer to congruences or some other strict similarity
  relations.

  > When defining a new target language, locally rename `＝`
  > to `≡` for definitional equalities of the target language if you
  > need so. Builtin Agda equality is called `_＝ⁱ_`.

- 3.3.3 The `→` **SHOULD** be used over `to`.

- 3.3.4 The `equiv` or `≃` **SHOULD** refer to equivalences of types or
  structures.

  > Operators can use subscript `ₑ`.

- 3.3.5 The `iso` or `≅` **SHOULD** refer to isomorphisms of types or
  structures.

  > Here an isomorphism is a function with a quasi-inverse,
  > i.e. a quasi-equivalence in the sense of the HoTT Book. Operators
  > can use subscript `ᵢ`.

- 3.3.6 The `Path` or `=` **SHOULD** refer to paths in names, not `Eq`, `Id`,
  or other "equality" or "identity"-related names.

  > Operators can use subscript `ₚ`.
