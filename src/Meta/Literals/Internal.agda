{-# OPTIONS --safe #-}
module Meta.Literals.Internal where

open import Agda.Builtin.FromNat public
  using ( Number )
  renaming ( fromNat to from-nat )

open import Agda.Builtin.FromNeg public
  using ( Negative )
  renaming ( fromNeg to from-neg )

open import Agda.Builtin.FromString public
  using ()
  renaming ( IsString   to is-string
           ; fromString to from-string )
