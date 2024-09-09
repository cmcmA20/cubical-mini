{-# OPTIONS --safe #-}
module Meta.Prelude where

-- `ₜ` for typal
open import Foundations.Prelude
  renaming ( _$²_ to _$ₜ²_
           ; _$³_ to _$ₜ³_
           ; _$⁴_ to _$ₜ⁴_
           )
  hiding ( case_of_
         ; case_return_of_
         )
  public

open import Meta.Effect    public
open import Meta.Inductive public
open import Meta.Variadic  public

open import Data.Bool.Base
  using ( H-Level-So )
open import Data.Nat.Order.Inductive.Base -- for H-Levels
  using ()
  renaming ( _≤_       to _≤ʰ_
           ; _≥_       to _≥ʰ_
           ; z≤        to z≤ʰ
           ; s≤s       to s≤ʰs
           ; s≤s′      to s≤ʰs′
           ; ≤-refl    to ≤ʰ-refl
           ; ≤-suc-r′  to ≤ʰ-suc-r′
           ; H-Level-≤ to H-Level-ℕ-≤
           )
  public
open import Data.Nat.Instances.FromNat public
