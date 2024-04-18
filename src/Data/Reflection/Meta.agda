{-# OPTIONS --safe #-}
module Data.Reflection.Meta where

open import Agda.Builtin.Reflection
  public
  using ( Meta
        ; Blocker
        )
  renaming ( primMetaEquality to _meta=?_
           ; primMetaLess     to _meta<?_
           ; primShowMeta     to show-meta
           ; primMetaToNat    to meta→ℕ

           ; blockerAny  to blocker-any
           ; blockerAll  to blocker-all
           ; blockerMeta to blocker-meta
           )
