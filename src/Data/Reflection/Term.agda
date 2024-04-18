{-# OPTIONS --safe #-}
module Data.Reflection.Term where

open import Foundations.Base

open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.String.Base

open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Abs

open import Agda.Builtin.Reflection
  public
  using ( Term ; var ; con ; def ; lam ; pat-lam ; pi ; agda-sort
          ; lit ; unknown
        ; Sort ; set ; prop ; inf
        ; Pattern ; dot ; proj ; absurd
        ; Clause ; clause ; absurd-clause
        ; Definition ; function ; data-type ; record-type ; data-cons
          ; axiom ; prim-fun
        )
  renaming ( propLit to prop-lit
           ; Type    to Type′ )

Telescope = List (String × Arg Term)

Args = List (Arg Term)
Patterns = List (Arg Pattern)

get-args : Term → Args
get-args (var x args) = args
get-args (con c args) = args
get-args (def f args) = args
get-args (pat-lam cs args) = args
get-args (meta x x₁) = x₁
get-args _ = []

get-abs : Term → Abs Term
get-abs (lam v t) = t
get-abs (pi a b)  = b
get-abs _ = abs "" unknown

clause→patterns : Clause → Patterns
clause→patterns (clause tel ps t) = ps
clause→patterns (absurd-clause tel ps) = ps

clause→term : Clause → Term
clause→term (clause tel ps t) = t
clause→term (absurd-clause tel ps) = unknown

pi-view : Term → Telescope × Term
pi-view (pi a (abs n b)) with pi-view b
... | tele , t = ((n , a) ∷ tele) , t
pi-view t = [] , t

pi-impl-view : Term → Telescope × Term
pi-impl-view t@(pi (arg (arg-info visible _) _) _) = [] , t
pi-impl-view (pi a (abs n b)) with pi-impl-view b
... | tele , t = ((n , a) ∷ tele) , t
pi-impl-view t = [] , t

unpi-view : Telescope → Term → Term
unpi-view []            k = k
unpi-view ((n , a) ∷ t) k = pi a (abs n (unpi-view t k))

tel→lam : Telescope → Term → Term
tel→lam []                                t = t
tel→lam ((n , arg (arg-info v _) _) ∷ ts) t = lam v (abs n (tel→lam ts t))

list-term : List Term → Term
list-term []       = con (quote List.[]) []
list-term (x ∷ xs) = con (quote List._∷_) (argN x ∷ argN (list-term xs) ∷ [])

list-pattern : Patterns → Pattern
list-pattern []       = con (quote List.[]) []
list-pattern (x ∷ xs) = con (quote List._∷_) (x ∷ argN (list-pattern xs) ∷ [])

pattern con₀ v = con v []
pattern def₀ v = def v []
pattern var₀ v = var v []
