{-# OPTIONS --safe #-}
module Structures.DoubleNegation.Instances.Idiom where

open import Foundations.Base
open import Meta.Idiom

open import Structures.DoubleNegation.Base public

instance
  Map-¬¬ : Map (eff ¬¬_)
  Map-¬¬ .Map._<$>_ f ¬¬a ¬b = ¬¬a λ a → ¬b (f a)

  Idiom-¬¬ : Idiom (eff ¬¬_)
  Idiom-¬¬ .Idiom.pure a ¬a = ¬a a
  Idiom-¬¬ .Idiom._<*>_ ¬¬f ¬¬a ¬b = ¬¬a (λ a → ¬¬f (λ f → ¬b (f a)))
