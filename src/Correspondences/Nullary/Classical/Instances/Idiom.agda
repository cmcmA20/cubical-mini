{-# OPTIONS --safe #-}
module Correspondences.Nullary.Classical.Instances.Idiom where

open import Foundations.Base

open import Meta.Idiom

open import Correspondences.Nullary.Classical.Base public

Classically = Classical

instance
  Map-Classically : Map (eff Classically)
  Map-Classically ._<$>_ f ¬¬a ¬b = ¬¬a λ a → ¬b (f a)

  Idiom-Classically : Idiom (eff Classically)
  Idiom-Classically .pure a ¬a = ¬a a
  Idiom-Classically ._<*>_ ¬¬f ¬¬a ¬b = ¬¬a (λ a → ¬¬f (λ f → ¬b (f a)))
