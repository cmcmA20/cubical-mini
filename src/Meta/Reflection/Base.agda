{-# OPTIONS --safe #-}
module Meta.Reflection.Base where

open import Foundations.Base

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Traverse
open import Data.Maybe.Base
open import Data.Nat.Instances.Number
open import Data.String.Base
open import Data.String.Instances.IsString

open import Meta.Literals    public
open import Meta.Idiom       public
open import Meta.Bind        public
open import Meta.Alt         public
open import Meta.Traverse    public
open import Meta.FromProduct public

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

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

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

id′ : (A : Type ℓ) → A → A
id′ A x = x

underAbs : Term → TC A → TC A
underAbs (lam v (abs nm _)) m = extendContext nm (arg (arg-info v (modality relevant quantity-ω)) unknown) m
underAbs (pi a (abs nm _)) m = extendContext nm a m
underAbs _ m = m

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

pattern _v∷_ t xs = arg (arg-info visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arg-info hidden (modality relevant quantity-ω)) t ∷ xs
pattern _hm∷_ t xs = arg (arg-info hidden (modality relevant _)) t ∷ xs

infixr 30 _v∷_ _h∷_ _hm∷_

infer-hidden : ℕ → List (Arg Term) → List (Arg Term)
infer-hidden zero xs = xs
infer-hidden (suc n) xs = unknown h∷ infer-hidden n xs

getName : Term → Maybe Name
getName (def x _) = just x
getName (con x _) = just x
getName _ = nothing

_name=?_ : Name → Name → Bool
x name=? y = primQNameEquality x y

_visibility=?_ : Visibility → Visibility → Bool
visible visibility=? visible = true
hidden visibility=? hidden = true
instance′ visibility=? instance′ = true
_ visibility=? _ = false

-- [TODO: Reed M, 06/05/2022] We don't actually use any fancy modalities
-- anywhere AFAICT, so let's ignore those.
_arg-info=?_ : ArgInfo → ArgInfo → Bool
arg-info v₁ m₁ arg-info=? arg-info v₂ m₂ = (v₁ visibility=? v₂)

arg=? : ∀ {a} {A : Type a} → (A → A → Bool) → Arg A → Arg A → Bool
arg=? eq=? (arg i₁ x) (arg i₂ y) = (i₁ arg-info=? i₂) and (eq=? x y)

-- We want to compare terms up to α-equivalence, so we ignore binder
-- names.
abs=? : ∀ {a} {A : Type a} → (A → A → Bool) → Abs A → Abs A → Bool
abs=? eq=? (abs _ x) (abs _ y) = eq=? x y

“refl” : Term
“refl” = def (quote refl) []

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
get-boundary tm = unapply-path tm >>= λ where
  (just (_ , x , y)) → pure (just (x , y))
  nothing            → pure nothing


debug! : ∀ {ℓ} {A : Type ℓ} → Term → TC A
debug! tm = typeError ("[DEBUG]: " ∷ termErr tm ∷ [])

quote-repr-macro : ∀ {ℓ} {A : Type ℓ} → A → Term →  TC ⊤
quote-repr-macro a hole = do
  tm ← quoteTC a
  repr ← quoteTC tm
  typeError $ "The term\n  "
    ∷ termErr tm
    ∷ "\nHas quoted representation\n  "
    ∷ termErr repr ∷ []

macro
  quote-repr! : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr! a = quote-repr-macro a

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
  strErr (nest nesting ("[" <> show-ℕ nesting <> "]  ")) ∷ es
  where
    _<>_ : String → String → String
    _<>_ = concat-str
    infixr 10 _<>_

    nest : ℕ → String → String
    nest zero s = s
    nest (suc x) s = nest x (s <> "  ")
