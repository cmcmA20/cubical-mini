CONTRIBUTING
============

We very much appreciate contributions in the form of pull requests (PRs).
When preparing a PR here are some general guidelines:

- Abstract and automate as much as you can! Performance and conciseness
  are top priorities, though feel free to generously sprinkle comments if
  the code becomes too dry.

- To test your changes before submission, run `make` at the top level,
  which will generate all required `Everything` files in
  `src/README.agda` and then typecheck the latter file.
  Or you can just run `make test`.

- Please read through and clean your code before making a PR. Clean
  code has reasonable line length (<100 characters), good indentation,
  appropriate amounts of comments and consistent naming.

- Local definitions should be put in `where`, `let-in` or `private` so
  that it is easy to see which are the main results of a file and
  which are just helper definitions.

- If the code is based on some paper add a reference to the version of
  the paper that the file follows in a comment at the top of the
  file. Avoid calling top-level definitions `thm123`, `lem321`, etc.,
  instead have informative names and put pointers to the theorems and
  lemmas in comments above the definition.

- For guidelines how to name things see
  [NAMING.md](https://github.com/cmcmA20/cubical-mini/blob/master/NAMING.md).

- Use `private variable` to quantify over universe levels at the top
  of the file. All definitions should be maximally universe
  polymorphic.

- Make reasonably many arguments implicit. If you find yourself having
  to provide some argument explicitly most of the time then it should
  not be implicit. The same applies the other way around, if some argument
  most often can be replaced by `_` then it should be made implicit.

- Use `Type ℓ` for universes (so `Set ℓ` is not allowed in order to
  avoid confusion with the type of h-sets).

- All files should start with

  `{-# OPTIONS --safe #-}`

  unless there is a good reason for it not to. The `--erased-cubical` and
  `--no-import-sorts` flags are added in the `cubical-mini.agda-lib` file.

- It is much easier for us to review and merge smaller and
  self-contained PRs. If a PR changes a lot of files all over the
  library then they will conflict with other PRs making it harder for
  us to merge them. It also takes longer to comment on the code
  if the PR is very big. If you have a large PR please consider
  splitting it into smaller parts that build on each other.

- Large refactoring, renaming, etc., should be done in designated PRs
  that only do one thing.

- Draft PRs are very appreciated so that we can discuss the code as it
  develops. It also helps with knowing who's working on what and
  reducing duplicate efforts. If your code contains postulates then it
  should be in a draft PR until the postulates have been filled in.

- We automatically check for whitespace in the end of lines using
  Travis. It is easy to configure emacs so that this is visible while
  editing files by adding `(setq-default show-trailing-whitespace t)`
  to `~/.emacs`. The command `M-x delete-trailing-whitespace` is also
  very useful. It is possible to add a hook that runs this command
  automatically when saving Agda files, by adding the following to your
  `~/.emacs`:
  ```
  ;; delete trailing whitespace before saving in agda-mode
  (defun agda-mode-delete-whitespace-before-save ()
    (when (eq major-mode 'agda2-mode)
      (delete-trailing-whitespace)))

  (add-hook 'before-save-hook #'agda-mode-delete-whitespace-before-save)
  ```

- Use copattern-matching when instantiating records for efficiency.
  This seems especially important when constructing `Iso`s.

- If typechecking starts becoming slow try to fix the efficiency
  problems directly. We don't want to merge files that are very slow
  to typecheck so they will have to optimized at some point and it's
  often much easier to fix these things directly. If you don't know
  what to try, make a draft PR and ask for help.

- It is often useful to give explicit names to the `Iso`, `Equiv` and `Path`
  version of a result. Try to avoid switching between these when
  constructing something, for instance if you want to construct a `Path`
  out of a series of `Iso`s then compose the `Iso`s first and then apply
  `iso-to-path` once instead of converting all of them to paths and
  composing them as paths.

- Unless a file is in the `Foundations` package you don't need to add it
  manually to the `Everything` file as it is automatically generated when
  running `make`.

- For folders with `Base` and `Properties` submodules, the `Base` file
  can contain some basic consequences of the main definition, but
  shouldn't include theorems that would require any additional imports outside
  of `Foundations`.

- Avoid importing `Foundations.Everything`; import only the modules in
  `Foundations` you are using. Be reasonably specific in general when
  importing.
  In particular, avoid importing useless files or useless renaming
  and try to group them by folder like `Foundations` or `Data`

  If possible, group imports in the following order: `Foundations`, `Meta`,
  `Structures`, `Correspondences`, `Data`, `Functions`, `Containers`.
  Inside the group use the lexicographical order.

- Avoid `public` imports, except in modules that are specifically meant
  to collect and re-export results from several modules.
  Those mostly reside in `Foundations` and `Meta`.

- Module dependency structure is stratified as follows:

  In `Foundations` and `Data.*.Base` you can import primitives/builtins and
  `Foundations` modules.
  Any other imports are prohibited, `Foundations` must be self-contained.

  In `Meta` you can import anything, just be precise, do not create
  unnecessary dependencies.

  Everywhere else you must only avoid importing primitives/builtins.

- Avoid creating folders like `Data`, `Records` or `HITs` only for the sake of
  collecting all the inductive types, records or HITs.
  When naming new folders, take inspiration in semantics or purpose of the
  target concept, not in its' Agda syntax.

- `Data` is the correct place for common programming data types and their
  properties. If you see that your "data type" is quite general, admits a rich
  theory (e.g. `Category` or any algebraic stuff) and is applicable to various
  other concepts, it should be moved to the top-level.

  For every (inductive) data type check that it has a recursor (`rec`),
  dependent eliminator (`elim`), universal property for mapping out
  (`universal`), path space characterization (`module Path`) and useful
  instances.

- Erase type indices if it's a well-known optimization. If needed, create
  multiple representations of the same type but with different runtime
  performance, document their relationship by defining conversions.

- Create multiple representations of the same type and document what proofs
  are easy in this representation, and why.

- Put equivalent representation of the same type in specific subfolders of the
  original type.
  Direct one should be default and have no suffix.
  Computational and inductive must have a corresponding suffix.
  For example see `Data.Fin` and `Data.Fin.Inductive`.
