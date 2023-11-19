{-# OPTIONS --safe #-}
module Meta.Reflection where

open import Foundations.Base

open import Meta.Literals.FromNat     public
open import Meta.Literals.FromString  public
open import Meta.Literals.FromProduct public

open import Meta.Idiom    public
open import Meta.Bind     public
open import Meta.Alt      public
open import Meta.Traverse public

open import Data.Bool.Base
open import Data.List.Base as List
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom
open import Data.List.Instances.Traverse
open import Data.List.Operations as List
open import Data.Maybe.Base
open import Data.Maybe.Instances.Idiom
open import Data.Nat.Base
open import Data.String.Base
open import Data.Vec.Base
open import Data.Vec.Operations.Inductive

open import Agda.Builtin.Reflection public
  renaming (Type to Type′)

instance
  String-ErrorPart : IsString ErrorPart
  String-ErrorPart .IsString.Constraint _ = ⊤
  String-ErrorPart .IsString.fromString s = strErr s

  Map-TC : Map (eff TC)
  Map-TC .Map._<$>_ f x = bindTC x λ x → returnTC (f x)

  Idiom-TC : Idiom (eff TC)
  Idiom-TC .Idiom.pure = returnTC
  Idiom-TC .Idiom._<*>_ f g = bindTC f λ f → bindTC g λ g → pure (f g)

  Bind-TC : Bind (eff TC)
  Bind-TC .Bind._>>=_ = bindTC

  Alt-TC : Alt (eff TC)
  Alt-TC .Alt.fail′ xs = typeError [ strErr xs ]
  Alt-TC .Alt._<|>_ = catchTC

  Map-Arg : Map (eff Arg)
  Map-Arg .Map._<$>_ f (arg ai x) = arg ai (f x)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : ℕ

arg-vis : ArgInfo → Visibility
arg-vis (arg-info v _) = v

arg-modality : ArgInfo → Modality
arg-modality (arg-info _ m) = m

argH0 argH argN : A → Arg A
argH  = arg (arg-info hidden (modality relevant quantity-ω))
argH0 = arg (arg-info hidden (modality relevant quantity-0))
argN  = arg (arg-info visible (modality relevant quantity-ω))

Fun : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
Fun A B = A → B

under-abs : Term → TC A → TC A
under-abs (lam v (abs nm _)) m = extendContext nm (arg (arg-info v (modality relevant quantity-ω)) unknown) m
under-abs (pi a (abs nm _))  m = extendContext nm a m
under-abs _ m = m

new-meta : Term → TC Term
new-meta ty = do
  mv ← checkType unknown ty
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr mv , " of type " , termErr ty ]
  pure mv

new-meta′ : Term → TC (Meta × Term)
new-meta′ ty = do
  tm@(meta mv _) ← checkType unknown ty
    where _ → typeError $ [ "impossible new-meta′" ]
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr tm , " of type " , termErr tm ]
  pure (mv , tm)

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

pattern vis-arg v t = arg (arg-info v (modality relevant quantity-ω)) t

pattern varg t = vis-arg visible t
pattern harg t = vis-arg hidden t
pattern iarg t = vis-arg instance′ t

pattern _v∷_ t xs = varg t ∷ xs
pattern _h∷_ t xs = harg t ∷ xs
pattern _hm∷_ t xs = arg (arg-info hidden (modality relevant _)) t ∷ xs
pattern _i∷_ t xs = iarg t ∷ xs

infixr 30 _v∷_ _h∷_ _hm∷_ _i∷_

infer-hidden : (m : ℕ) → Vec (Arg Term) n → Vec (Arg Term) (m + n)
infer-hidden 0 xs = xs
infer-hidden (suc n) xs = harg unknown ∷ infer-hidden n xs

infer-hidden′ : (m : ℕ) → List (Arg Term) → List (Arg Term)
infer-hidden′ 0 xs = xs
infer-hidden′ (suc n) xs = harg unknown ∷ infer-hidden′ n xs

get-args : Term → List (Arg Term)
get-args (var _ args) = args
get-args (con _ args) = args
get-args (def _ args) = args
get-args (pat-lam _ args) = args
get-args _ = []

get-name : Term → Maybe Name
get-name (def x _) = just x
get-name (con x _) = just x
get-name _ = nothing

_name=?_ : Name → Name → Bool
x name=? y = primQNameEquality x y

_visibility=?_ : Visibility → Visibility → Bool
visible   visibility=? visible   = true
hidden    visibility=? hidden    = true
instance′ visibility=? instance′ = true
_         visibility=? _         = false

_relevance=?_ : Relevance → Relevance → Bool
relevant   relevance=? relevant   = true
irrelevant relevance=? irrelevant = true
_          relevance=? _          = false

_quantity=?_ : Quantity → Quantity → Bool
quantity-0 quantity=? quantity-0 = true
quantity-ω quantity=? quantity-ω = true
_          quantity=? _          = false

_modality=?_ : Modality → Modality → Bool
modality r₁ q₁ modality=? modality r₂ q₂ = (r₁ relevance=? r₂) and (q₁ quantity=? q₂)

_arg-info=?_ : ArgInfo → ArgInfo → Bool
arg-info v₁ m₁ arg-info=? arg-info v₂ m₂ = (v₁ visibility=? v₂) and (m₁ modality=? m₂)

arg=? : ∀ {a} {A : Type a} → (A → A → Bool) → Arg A → Arg A → Bool
arg=? eq=? (arg i₁ x) (arg i₂ y) = (i₁ arg-info=? i₂) and (eq=? x y)

-- We want to compare terms up to α-equivalence, so we ignore binder
-- names.
abs=? : ∀ {a} {A : Type a} → (A → A → Bool) → Abs A → Abs A → Bool
abs=? eq=? (abs _ x) (abs _ y) = eq=? x y

_term′=?_ : {n : ℕ} → Term → Term → Bool
_term′=?_ {0} _ _ = false
_term′=?_ {suc n} (var nm₁ args₁) (var nm₂ args₂)
  = (nm₁ == nm₂) and all=? (arg=? (_term′=?_ {n})) args₁ args₂
_term′=?_ {suc n} (con c₁ args₁) (con c₂ args₂) =
  (c₁ name=? c₂) and (all=? (arg=? (_term′=?_ {n})) args₁ args₂)
_term′=?_ {suc n} (def f₁ args₁) (def f₂ args₂) =
  (f₁ name=? f₂) and (all=? (arg=? (_term′=?_ {n})) args₁ args₂)
_term′=?_ {suc n} (lam v₁ t₁) (lam v₂ t₂) =
  (v₁ visibility=? v₂) and (abs=? (_term′=?_ {n}) t₁ t₂)
_term′=?_ {suc n} (pat-lam cs₁ args₁) (pat-lam cs₂ args₂) = false
_term′=?_ {suc n} (pi a₁ b₁) (pi a₂ b₂) =
  (arg=? (_term′=?_ {n}) a₁ a₂) and (abs=? (_term′=?_ {n}) b₁ b₂)
agda-sort s term′=? t₂ = false
lit l term′=? t₂ = false
meta x x₁ term′=? t₂ = false
unknown term′=? t₂ = false
_ term′=? _ = false

_term=?_ : Term → Term → Bool
_term=?_ = _term′=?_ {n = 1234567890} -- ;-)

“refl” : Term
“refl” = def (quote refl) []

“Path” : Term → Term → Term → Term
“Path” A x y = def (quote Path) (unknown h∷ A v∷ x v∷ y v∷ [])

wait-for-args : List (Arg Term) → TC (List (Arg Term))
wait-for-type : Term → TC Term

wait-for-type (var x args) = var x <$> wait-for-args args
wait-for-type (con c args) = con c <$> wait-for-args args
wait-for-type (def f args) = def f <$> wait-for-args args
wait-for-type (lam v (abs x t)) = pure (lam v (abs x t))
wait-for-type (pat-lam cs args) = pure (pat-lam cs args)
wait-for-type (pi (arg i a) (abs x b)) = do
  a ← wait-for-type a
  b ← wait-for-type b
  pure (pi (arg i a) (abs x b))
wait-for-type (agda-sort s) = pure (agda-sort s)
wait-for-type (lit l) = pure (lit l)
wait-for-type (meta x x₁) = blockOnMeta x
wait-for-type unknown = pure unknown

wait-for-args [] = pure []
wait-for-args (arg i a ∷ xs) = ⦇ ⦇ (arg i) (wait-for-type a) ⦈ ∷ wait-for-args xs ⦈

wait-just-a-bit : Term → TC Term
wait-just-a-bit (meta m _) = blockOnMeta m
wait-just-a-bit tm = pure tm

unapply-path : Term → TC (Maybe (Term × Term × Term))
unapply-path red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) = do
  domain ← new-meta (def (quote Type) (l v∷ []))
  ty ← pure (def (quote Path) (domain v∷ x v∷ y v∷ []))
  debugPrint "tactic" 50
    [ "(no reduction) unapply-path: got a "
    , termErr red
    , " but I really want it to be "
    , termErr ty
    ]
  unify red ty
  pure (just (domain , x , y))
unapply-path tm = reduce tm >>= λ where
  tm@(meta _ _) → do
    dom ← new-meta (def (quote Type) (unknown v∷ []))
    l ← new-meta dom
    r ← new-meta dom
    unify tm (def (quote Path) (dom v∷ l v∷ r v∷ []))
    traverse wait-for-type (l ∷ r ∷ [])
    pure (just (dom , l , r))
  red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) → do
    domain ← new-meta (def (quote Type) (l v∷ []))
    ty ← pure (def (quote Path) (domain v∷ x v∷ y v∷ []))
    debugPrint "tactic" 50
      [ "unapply-path: got a "
      , termErr red
      , " but I really want it to be "
      , termErr ty
      ]
    unify red ty
    pure (just (domain , x , y))
  _ → returnTC nothing

get-boundary : Term → TC (Maybe (Term × Term))
get-boundary tm = unapply-path tm >>= (pure ∘ (snd <$>_))


debug! : Term → TC A
debug! tm = typeError ("[DEBUG]: " ∷ termErr tm ∷ [])

quote-repr-macro : Bool → A → Term →  TC ⊤
quote-repr-macro norm? a hole = do
  tm ← quoteTC a
  repr ← (if norm? then normalise else pure) tm >>= quoteTC
  typeError $ "The term\n  "
    ∷ termErr tm
    ∷ "\nHas quoted representation\n  "
    ∷ termErr repr ∷ []

macro
  quote-repr! : {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr! = quote-repr-macro false

  quote-repr-norm! : {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr-norm! = quote-repr-macro true

instance
  IsString-Error : IsString (List ErrorPart)
  IsString-Error .IsString.Constraint _ = ⊤
  IsString-Error .from-string s = from-string s ∷ []

unify-loudly : Term → Term → TC ⊤
unify-loudly a b = do
  debugPrint "tactic" 50 $ termErr a ∷ " =? " ∷ termErr b ∷ []
  unify a b

print-depth : String → ℕ → ℕ → List ErrorPart → TC ⊤
print-depth key level nesting es = debugPrint key level $
  strErr (nest nesting ("[" ++ₛ show-ℕ nesting ++ₛ "]  ")) ∷ es
  where
    nest : ℕ → String → String
    nest zero    s = s
    nest (suc x) s = nest x (s ++ₛ "  ")

pattern nat-lit n =
  def (quote Number.fromNat) (_ ∷ _ ∷ _ ∷ lit (nat n) v∷ _)

suc-term : Term → Term
suc-term (lit (nat n)) = lit (nat (suc n))
suc-term t = con (quote suc) (t v∷ [])

pred-term : Term → Maybe Term
pred-term (con (quote suc) (x v∷ [])) = just x
pred-term (lit (nat n)) with n
... | suc k = just (lit (nat k))
... | _ = nothing
pred-term _ = nothing

plus-term : Term → Term → Term
plus-term (nat-lit 0) (nat-lit n) = lit (nat n)
plus-term (nat-lit m) (nat-lit 0) = lit (nat m)
plus-term (lit (nat 0)) (lit (nat n)) = lit (nat n)
plus-term (lit (nat m)) (lit (nat 0)) = lit (nat m)
plus-term (lit (nat m)) (lit (nat n)) = lit (nat (m + n))
plus-term x y = def (quote _+_) (x v∷ y v∷ [])

-- working under lambda

leave : Telescope → Term → Term
leave [] = id
leave ((na , arg as _) ∷ xs) = leave xs ∘ lam (arg-vis as) ∘ abs na

enter : Telescope → TC A → TC A
enter [] = id
enter ((na , ar) ∷ xs) = enter xs ∘ extendContext na ar

-- returns free variables as de Bruijn indices in the _current_ context
-- same order as in input term, has duplicates
fv-dup : Term → List ℕ
fv-dup = go 0 where
  go : ℕ → Term → List ℕ
  go* : ℕ → List (Arg Term) → List ℕ

  go nbind (var v args) =
    if nbind <ᵇ suc v
       then (v ∸ nbind) ∷_
       else id
     $ go* nbind args
  go nbind (con _ args) = go* nbind args
  go nbind (def _ args) = go* nbind args
  go nbind (lam _ (abs _ x)) = go (suc nbind) x
  go nbind (pi (arg _ x) (abs _ y)) =
    go nbind x List.++ go (suc nbind) y
  go _   _ = []

  go* _ [] = []
  go* nbind (arg _ x ∷ xs) =
    go nbind x List.++ go* nbind xs

fv     = nub-slow _==_ ∘ fv-dup
fv-ord = nub-unsafe _==_ ∘ insertion-sort (λ m n → m <ᵇ suc n) ∘ fv-dup
