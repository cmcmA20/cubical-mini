{-# OPTIONS --safe #-}
module Prim.Interval where

open import Prim.Type

open import Agda.Primitive.Cubical public
  using ( IUniv -- IUniv : SSet₁
        ; I     -- I : IUniv
        ; i0    -- i0 : I
        ; i1    -- i1 : I
        ; IsOne -- IsOne : I → Typeω
        ; Partial -- Partial : ∀{ℓ} (i : I) (A : Type ℓ) → Type ℓ
                  -- Partial i A = IsOne i → A
        ; PartialP
        ; primPOr )
  renaming ( primIMin to _∧_ -- _∧_ : I → I → I
           ; primIMax to _∨_ -- _∨_ : I → I → I
           ; primINeg to ~_  -- ~_ : I → I

           ; itIsOne    to 1=1       -- 1=1 : IsOne i1
           ; isOneEmpty to is1-empty -- is1-empty : ∀ {ℓ} {A : Partial i0 (Type ℓ)} → PartialP i0 A
           ; IsOne1     to is1-left  -- is1-left  : ∀ i j → IsOne i → IsOne (i ∨ j)
           ; IsOne2     to is1-right -- is1-right : ∀ i j → IsOne j → IsOne (i ∨ j)
           )
