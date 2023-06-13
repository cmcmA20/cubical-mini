{-# OPTIONS --safe #-}
module Data.List.Instances.Bind where

open import Foundations.Base

open import Meta.Bind

open import Data.List.Instances.Idiom public

instance
  Bind-List : Bind (eff List)
  Bind-List .Bind._>>=_ = go where
    go : _
    go []       _ = []
    go (x ∷ xs) f = f x ++ go xs f
