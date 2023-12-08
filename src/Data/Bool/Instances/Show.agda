{-# OPTIONS --safe #-}
module Data.Bool.Instances.Show where

open import Meta.Show

open import Data.Bool.Base

instance
  Show-bool : Show Bool
  Show-bool = default-show go where
    go : Bool → _
    go false = "false"
    go true  = "true"
