{-# OPTIONS --safe #-}
module Meta.Deriving.Show where

open import Foundations.Base

open import Meta.Append
open import Meta.Effect.Traversable
open import Meta.Reflection.Base
open import Meta.Reflection.Signature
open import Meta.Show public

open import Data.Bool.Base
open import Data.Char.Base
open import Data.Float.Instances.FromNat
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Instances.Map
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Traversable
open import Data.Nat.Base
open import Data.String.Base
open import Data.String.Instances.Append


private
  -- Parts of a mixfix name.
  data Name-part : Type where
    -- An underscore.
    hole : Precedence → Name-part

    -- An identifier part.
    name : String     → Name-part

  -- Parse a name to a list of its parts.
  name→parts : String → List Name-part
  name→parts = go full-tank ∘ string→list where
    not-under : Char → Bool
    not-under '_' = false
    not-under _   = true

    go : ℕ → List Char → List Name-part
    go 0 _ = []
    go (suc fuel) []         = []
    go (suc fuel) ('_' ∷ cs) = hole unrelated ∷ go fuel cs
    go (suc fuel) (c   ∷ cs) =
      let (p , r) = span not-under (c ∷ cs)
       in name (list→string p) ∷ go fuel r

  -- Intermediate representation for the values to be concatenated when
  -- generating a clause for the Show instance.
  data Shown : Type where
    lits : String → Shown
    term : Term   → Shown

  -- Cons a 'lits' onto the list, but reduce adjacent 'lits'.
  cons-lits : String → List Shown → List Shown
  cons-lits x []            = lits x ∷ []
  cons-lits x (lits y ∷ xs) = cons-lits (x <> y) xs
  cons-lits x (term t ∷ xs) = lits x ∷ term t ∷ xs

  -- Reduce any adjacent 'lits' the given list.
  reduce-shown : List Shown → List Shown
  reduce-shown (lits x ∷ xs) = cons-lits x (reduce-shown xs)
  reduce-shown (term t ∷ xs) = term t ∷ reduce-shown xs
  reduce-shown []            = []

  quote-prec : Precedence → Term
  quote-prec (related x) = it related ##ₙ lit (float x)
  quote-prec unrelated   = it unrelated

  -- Given a list of name parts, and a list of terms standing for the
  -- arguments to that name, return a list of 'Shown' values in which
  -- the arguments are properly interspersed the parts of the name.
  zip-shown : List Name-part → List Term → List Shown
  zip-shown (hole p ∷ ps) (t ∷ ts) =
    let t = itₙ shows-prec (quote-prec p) t
     in term t ∷ zip-shown ps ts
  zip-shown (hole p ∷ ps) [] = []
  zip-shown (name n ∷ ps) ts = cons-lits n (zip-shown ps ts)
  zip-shown []            ts = []

  -- Given the precedence to be used for the context and for the
  -- arguments of the constructor under consideration, propagate the
  -- context's precedence to the hole which corresponds to the direction
  -- of associativity.
  --
  -- This ensures that e.g. `show (1 , 2 , 3)` will be `(1 , 2 , 3)`,
  -- rather than `(1 , (2 , 3))`, since the second argument of `_,_`
  -- will be rendered with the same precedence as the overall
  -- expression.
  assoc-name-parts : Associativity → Precedence → Precedence → List Name-part → List Name-part
  assoc-name-parts left-assoc thisp argp (hole _ ∷ p ∷ hole _ ∷ []) =
    hole thisp ∷ p ∷ hole argp ∷ []
  assoc-name-parts right-assoc thisp argp (hole _ ∷ p ∷ hole _ ∷ []) =
    hole argp ∷ p ∷ hole thisp ∷ []
  assoc-name-parts a thisp argp ps = ps

  -- Convert a list of 'Shown' values to the Term standing for their
  -- concatenation.
  from-shown-list : List Shown → Term
  from-shown-list []                = it mempty
  from-shown-list (lits x ∷ [])     = itₙ from-string (lit (string x))
  from-shown-list (term x ∷ [])     = x
  from-shown-list (lits x ∷ y ∷ xs) = itₙ _<>_
    (itₙ from-string (lit (string x)))
    (from-shown-list (y ∷ xs))
  from-shown-list (term x ∷ y ∷ xs) = itₙ _<>_ x (from-shown-list (y ∷ xs))

  -- Create the clause of shows-prec for a constructor.
  show-clause : Constructor → TC Clause
  show-clause (conhead conm _ args _) = do
    let
      -- We'll only show the visible arguments to the constructor.
      -- Moreover, since Agda can infer the types in the telescope
      -- better than we can specify them here, we replace everything
      -- with `unknown`.
      tele : List (String × Arg Term)
      tele = map (second (map λ _ → unknown)) $
        filter (λ { (_ , arg (arg-info visible _) _) → true
                  ; _ → false
                  })
         args
      ixs  = reverse-fast (map-up (λ i _ → i) 0 tele)

    -- The constructor should be rendered as a concrete name in scope,
    -- rather than a fully-qualified name.
    con-str ← render-name conm

    fixity thisa thisp ← pure $ name→fixity conm
    let argp = suc-precedence thisp

    let
      shown₀ = map (itₙ shows-prec (it unrelated) ∘ var₀) ixs
      parts  = assoc-name-parts thisa thisp argp (name→parts con-str)

      holes  = length (filter (λ { (hole _) → true ; _ → false }) parts)

      -- The strategy for the generated clause is as follows: if we have
      -- a mixfix name with as many holes as the constructor has visible
      -- arguments, then we'll show the constructor infix, using
      -- `zip-shown` above. Otherwise, we'll display it prefix.

      shown =
        if holes == length shown₀
          then zip-shown parts (var₀ <$> ixs)
          else cons-lits con-str (map term shown₀)

      inner = from-shown-list (reduce-shown (intercalate (lits " ") shown))

      -- But that's not the complete clause: we must also wrap the shown
      -- value in parentheses, according to the precedence of the
      -- context, *unless* the constructor is nullary. Parentheses are
      -- shown if the precedence of the context is greater than the
      -- precedence of the constructor name, as returned by name→fixity.

      guard = itₙ prec-parens (var₀ (length tele)) (quote-prec thisp)

      tm = case shown₀ of λ where
        [] → itₙ from-string (lit (string con-str))
        _  → itₙ show-parens guard inner

    pure $
      clause (("prec" , argN (it Precedence)) ∷ tele)
        [ argN (var (length tele))
        , argN (con conm (map (argN ∘ var) ixs))
        ]
        tm

-- Derives an instance of 'Show' for a datatype or record. This function
-- works whether or not the instance has previously been defined.

derive-show : Name → Name → TC ⊤
derive-show nm dat = do
  is-defined nm >>= λ where
    false → declare-def (argI nm) =<< instance-type (it Show ##_) dat
    true  → pure tt

  cons ← get-type-constructors dat
  (tel , as) ← instance-telescope (it Show ##_) dat
  let ty = unpi-view tel $ itₙ Fun (it Precedence) (itₙ Fun (def dat as) (it ShowS))
  work ← helper-function nm "go" ty []

  define-function nm $
    [ clause [] [] (`constructor Show
      ##ₙ def₀ work
      ##ₙ lam visible (abs "x"
        (itₙ ShowS.unshowS
          (def₀ work ##ₙ quote-prec (related 0) ##ₙ var₀ 0)
          (lit (string "")))))
    ]

  define-function work =<< traverse show-clause cons


instance unquoteDecl Show-Σ = derive-show Show-Σ (quote Σ)
