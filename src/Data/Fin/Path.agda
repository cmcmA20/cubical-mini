{-# OPTIONS --safe #-}
module Data.Fin.Path where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Nat.Base
open import Data.Maybe.Base
  using ()
  renaming ( is-just?    to is-fsuc?
           ; is-nothing? to is-fzero?
           )
  public
open import Data.Maybe.Path
  using ( maybe-is-of-hlevel
        ; ¬→maybe-is-contr )
open import Data.Maybe.Path
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

opaque
  fin-is-set : is-set (Fin n)
  fin-is-set {0}     = hlevel 2
  fin-is-set {suc n} = maybe-is-of-hlevel 0 fin-is-set

instance
  H-Level-Fin1 : H-Level k (Fin 1)
  H-Level-Fin1 = hlevel-basic-instance 0 (¬→maybe-is-contr λ ())
  {-# INCOHERENT H-Level-Fin1 #-}
