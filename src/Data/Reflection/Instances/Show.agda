{-# OPTIONS --safe #-}
module Data.Reflection.Instances.Show where

open import Meta.Show

open import Data.Reflection.Meta
open import Data.Reflection.Name

instance
  Show-Meta : Show Meta
  Show-Meta = default-show show-meta

  Show-Name : Show Name
  Show-Name = default-show show-name
