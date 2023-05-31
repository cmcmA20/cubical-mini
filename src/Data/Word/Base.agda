{-# OPTIONS --safe #-}
module Data.Word.Base where

open import Agda.Builtin.Word public
  using ( Word64 )
  renaming ( primWord64ToNat   to word64→ℕ
           ; primWord64FromNat to ℕ→word64 )
