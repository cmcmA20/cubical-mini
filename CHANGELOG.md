Version 0.5
===============

The library has been tested using Agda master (0ff0741244252b46a183b7d5d4f526b7fe8c25f7)

Highlights
----------

* Reflexivity/symmetry/transitivity is now instance-based; it significantly
  reduces notation overhead (and slightly worsens typechecking time).

* All specific reasoning combinators and syntax are removed in favour of generic
  relational syntax (also instance-based).

* `Refl` and `Reflexive` made into a record. `refl` is a proof of reflexivity for
  any correspondence having a `Refl` instance.
  `Symm` and `Symmetric` made into a record. `_⁻¹` is a proof of symmetry for
  any correspondence having a `Symm` instance.
  `Trans` and `Transitive` made into a record. `_∙_` is a proof of transitivity for
  any correspondence having a `Trans` instance.

Bug-fixes
---------

* Fix `ap!` (and `ap¡`) macro, now it blocks until the type of an equation is
  known.

Non-backwards compatible changes
--------------------------------
Most of the changes in this release are not backwards compatible.

Other major improvements
------------------------

* Folder structure now conforms to project design, concepts are roughly
  clustered by math area.

* Ubiquitous instance automation instead of macros wherever possible.

Minor improvements
------------------
* The size of the dependency graph for many modules has been
  reduced. This may lead to speed ups for first-time loading of some
  modules.

* Using internal prelude (`Meta.Prelude`) almost everywhere.

* `Refl`, `Symm`, `Trans` instances for categories, displayed categories,
  posets, algebraic structures. Monoid, group, category notation are
  instantiations of generic combinators.

Deprecated modules
------------------

* `Correspondences.Base` removed. Its' content is split between
  `Foundations.Correspondences.*` and `Foundations.Equiv.Base`.

* `Correspondences.Separated` removed. Its' content is split between
  `Logic.Discreteness` and `Foundations.Equiv.Base`.

* | Old name                        | New name                       |
  | ------------------------------- | ------------------------------ |
  | `Correspondences.Classical`     | `Logic.DoubleNegation`         |
  | `Correspondences.Connected`     | `Homotopy.Connectedness`       |
  | `Correspondences.Countable.*`   | `Combinatorics.Countability.*` |
  | `Correspondences.Decidable`     | `Logic.Decidability`           |
  | `Correspondences.Discrete`      | `Logic.Discreteness`           |
  | `Correspondences.Exhaustible`   | `Logic.Exhaustibility`         |
  | `Correspondences.Omniscient`    | `Logic.Omniscience`            |
  | `Correspondences.Powerset.*`    | `Combinatorics.Power.*`        |
  | `Correspondences.Wellfounded.*` | `Data.Wellfounded`             |

* `Containers` deprecated in favour of `Data.Container`.

* `Truncations` deprecated in favour of `Data.Truncation.*`.

* `Meta.Append` and `Meta.Groupoid` subsumed by new classes in
  `Foundations.Correspondences.*`.

Deprecated names
----------------

A ton.

New modules
-----------

* Oxford brackets notation:
  ```
  Meta.Brackets
  ```

* Macros for manipulating copattern definitions:
  ```
  Meta.Copattern
  ```

* Macros for projecting properties from records:
  ```
  Meta.Projection
  ```

* Macros for deriving eliminator for (higher) inductive types:
  ```
  Meta.Deriving.Elim
  ```

* Macros for deriving hlevel of records:
  ```
  Meta.Deriving.HLevel
  ```

* Macros for manipulating reflected arguments:
  ```
  Meta.Reflection.Argument
  ```

* Macros for neutral application in reflection:
  ```
  Meta.Reflection.Neutral
  ```
