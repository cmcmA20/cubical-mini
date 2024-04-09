{-# OPTIONS --safe #-}
module Foundations.Prelude where

open import Foundations.Base public
  renaming ( singleton-is-contr  to singletonₜ-is-contr
           ; singletonᴾ-is-contr to singletonₜᴾ-is-contr

           ; J       to Jₜ
           ; J-refl  to Jₜ-refl
           ; J-∙     to Jₜ-∙
           ; Jᵈ      to Jₜᵈ
           ; Jᵈ-refl to Jₜᵈ-refl
           ; J²      to Jₜ²
           ; J²-refl to Jₜ²-refl
           ; J>_     to Jₜ>_
           )

open import Foundations.Cubes      public
open import Foundations.Erased     public
open import Foundations.HLevel     public
open import Foundations.Path       public
open import Foundations.Pi         public
open import Foundations.Sigma      public
open import Foundations.Transport  public
open import Foundations.Univalence public

open import Foundations.IdentitySystem.Interface public
