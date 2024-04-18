{-# OPTIONS --safe #-}
module Data.Reflection.Error where

open import Agda.Builtin.Reflection
  public
  using ( ErrorPart
        )
  renaming ( strErr  to str-err
           ; termErr to term-err
           ; pattErr to pat-err
           ; nameErr to name-err
           )
