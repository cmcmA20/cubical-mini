{-# OPTIONS --safe #-}
module Containers.List.Base where

open import Foundations.Base

open import Data.Nat.Base
open import Data.FinSum.Base

open import Containers.Base public

ListC : Container 0ℓ 0ℓ
ListC = ℕ ▶ Fin

List : {ℓ : Level} → Type ℓ → Type ℓ
List = ⟦ ListC ⟧
