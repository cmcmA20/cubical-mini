{-# OPTIONS --safe #-}
module Meta.Reflection.SIP where

open import Foundations.Base

open import Data.List.Base
open import Data.Nat.Base
open import Data.Nat.Instances.Number
open import Data.String.Instances.IsString

open import Meta.Reflection.Base
open import Meta.SIP

makeAutoStr-term : ℕ → Term → TC ⊤
makeAutoStr-term zero t = typeError (strErr "autoDesc ran out of fuel" ∷ [])
makeAutoStr-term (suc n) t =
  tryPoint
    <|> tryBin (quote _s→_)
    <|> tryBin (quote _s×_)
    <|> useConst
  where
    tryPoint = do
      unify t (con (quote s∙) [])

    tryBin : Name → TC ⊤
    tryBin namen = do
      h1 ← new-meta unknown
      h2 ← new-meta unknown
      tt ← unify (con namen (h1 v∷ h2 v∷ [])) t
      tt ← makeAutoStr-term n h1
      makeAutoStr-term n h2

    useConst = do
      unify t (con (quote s-const) (unknown v∷ []))

macro
  auto-str-term : Term → TC ⊤
  auto-str-term = makeAutoStr-term 100
