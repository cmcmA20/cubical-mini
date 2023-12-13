{-# OPTIONS --safe #-}
module Data.Fin.Path where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.Nat.Base
open import Data.Maybe.Base
  using ()
  renaming ( is-just    to is-fsuc
           ; is-nothing to is-fzero)
  public
open import Data.Maybe.Path using (maybe-is-of-hlevel)
open import Data.Maybe.Path
  using ( Code
        ; code-refl
        ; identity-system
        ; code-is-of-hlevel
        )
  renaming ( nothing≠just      to fzero≠fsuc
           ; just≠nothing      to fsuc≠fzero
           ; just-inj          to fsuc-inj
           ; just-cancellable  to fsuc-cancellable
           ; just-is-embedding to fsuc-is-embedding
           )
  public

open import Data.Fin.Base

private variable
  n : ℕ
  k : HLevel

fin-is-set : is-set (Fin n)
fin-is-set {0}     = hlevel!
fin-is-set {suc n} = maybe-is-of-hlevel _ fin-is-set

instance
  H-Level-fin : H-Level (2 + k) (Fin n)
  H-Level-fin = hlevel-basic-instance 2 fin-is-set

fin-is-of-hlevel : (k : HLevel) → is-of-hlevel (2 + k) (Fin n)
fin-is-of-hlevel _ = hlevel _

instance
  decomp-hlevel-fin : goal-decomposition (quote is-of-hlevel) (Fin n)
  decomp-hlevel-fin = decomp (quote fin-is-of-hlevel) [ `level-minus 2 ]
