{-# OPTIONS --safe #-}
module Meta.Extensionality where

open import Foundations.Base
  hiding (_$_)
open import Foundations.Equiv
open import Foundations.Sigma

open import Meta.Effect.Alt
open import Meta.Reflection.Base
open import Meta.Reflection.Signature
open import Meta.Reflection.Subst
open import Meta.Search.HLevel
open import Meta.Variadic

open import Structures.IdentitySystem.Base
  hiding (J; J-refl)
  public
open import Structures.n-Type

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Instances.Alt


record Extensional {ℓ} (A : Type ℓ) (ℓ-rel : Level) : Typeω where
  no-eta-equality
  field
    Pathᵉ : A → A → Type ℓ-rel
    reflᵉ : ∀ x → Pathᵉ x x
    idsᵉ  : is-identity-system Pathᵉ reflᵉ

record Extensionality {ℓ} (A : Type ℓ) : Type where
  field lemma : Name

open Extensional using (Pathᵉ ; reflᵉ ; idsᵉ) public

private variable ℓ ℓ′ : Level

-- Default instance, uses regular paths for the relation.
Extensional-default : {A : Type ℓ} → Extensional A ℓ
Extensional-default .Pathᵉ   = _＝_
Extensional-default .reflᵉ _ = refl
Extensional-default .idsᵉ    = path-identity-system

-- Find a value of 'Extensional' by looking at instances of 'Extensionality'.
find-extensionality : Term → TC Term
find-extensionality tm = do
  -- We have to block on the full type being available to prevent a
  -- situation where the default instance (or an incorrect instance!) is
  -- picked because the type is meta-headed.
  tm ← reduce =<< wait-for-type tm
  let search = it Extensionality ##ₙ tm
  debug-print "tactic.extensionality" 10 [ "find-extensionality goal:\n  " , termErr search ]

  resetting do
    (mv , _) ← new-meta′ search
    get-instances mv >>= λ where
      (x ∷ _) → do
        t ← unquoteTC {A = Name} =<< normalise (it Extensionality.lemma ##ₙ x)
        debug-print "tactic.extensionality" 10 (" ⇒ found lemma " ∷ nameErr t ∷ [])
        pure (def₀ t)
      [] → do
        debug-print "tactic.extensionality" 10 " ⇒ using default"
        pure (it Extensional-default)

-- Entry point for getting hold of an 'Extensional' instance:
extensional : (A : Type ℓ) → Term → TC ⊤
extensional A goal = do
  `A ← quoteTC A
  check-type goal (def (quote Extensional) [ argN `A , argN unknown ])
  unify goal =<< find-extensionality `A

{-
Unlike extensional, which is parametrised by a type, extensionalᶠ
can be parametrised by a function (of arbitrary arity) into types,
even though its type doesn't properly reflect this. It will discharge
goals like

   ∀ x → Extensional (P x) ℓ

by getting rid of every Π in the type and looking in an extended
context. It's also possible to use ⦃ _ : ∀ {x} → Extensional (P x) ℓ ⦄,
since Agda supports commuting those by itself. However, using
extensionalᶠ blocks more aggressively, which is required for touchy
instances like Extensional-natural-transformation.
-}
extensionalᶠ : {A : Type ℓ} → A → Term → TC ⊤
extensionalᶠ {A} fun goal = ⦇ wrap (quoteTC A) (quoteTC fun) ⦈ >>= id where
  work : Term → Term → TC Term
  work (pi dom@(arg ai _) (abs nm cod)) tm = do
    prf ← extend-context nm dom do
      tm ← maybe→alt $ raise 1 tm <#> arg ai (var₀ 0)
      work cod tm
    pure (lam (arg-vis ai) (abs nm prf))
  work _ tm = find-extensionality tm

  wrap : Term → Term → TC ⊤
  wrap t fn = do
    t ← wait-for-type t
    debug-print "tactic.extensionality" 10
      [ "extensionalᶠ goal:\n  " , termErr fn , "\nof type\n  " , termErr t ]
    prf ← work t fn
    unify goal prf

instance
  extensional-extensionality
    : ∀ {ℓ ℓs} {A : Type ℓ} {@(tactic extensional A) sa : Extensional A ℓs}
    → Extensional A ℓs
  extensional-extensionality {sa} = sa

{-
Canonical example of extending the Extensionality tactic:

* The actual 'Extensional' value can have ⦃ Extensional A ℓ ⦄ in its
  "instance context". These are filled in by the bridge instance above.

* The 'Extensionality' loop-breaker only mentions the things that are
  actually required to compute the "head" type.
-}
Extensional-Lift
  : ∀ {ℓr} {A : Type ℓ}
  → ⦃ sa : Extensional A ℓr ⦄
  → Extensional (Lift ℓ′ A) ℓr
Extensional-Lift ⦃ sa ⦄ .Pathᵉ (lift x) (lift y) = sa .Pathᵉ x y
Extensional-Lift ⦃ sa ⦄ .reflᵉ (lift x) = sa .reflᵉ x
Extensional-Lift ⦃ sa ⦄ .idsᵉ .to-path p = ap lift (sa .idsᵉ .to-path p)
Extensional-Lift ⦃ sa ⦄ .idsᵉ .to-path-over p = sa .idsᵉ .to-path-over p

instance
  extensionality-lift : {A : Type ℓ} → Extensionality (Lift ℓ′ A)
  extensionality-lift .Extensionality.lemma = quote Extensional-Lift

Extensional-Π
  : ∀ {ℓ ℓ′ ℓr} {A : Type ℓ} {B : A → Type ℓ′}
  → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
  → Extensional Π[ B ] (ℓ ⊔ ℓr)
Extensional-Π ⦃ sb ⦄ .Pathᵉ f g = ∀ x → Pathᵉ sb (f x) (g x)
Extensional-Π ⦃ sb ⦄ .reflᵉ f x = reflᵉ sb (f x)
Extensional-Π ⦃ sb ⦄ .idsᵉ .to-path h = fun-ext λ i → sb .idsᵉ .to-path (h i)
Extensional-Π ⦃ sb ⦄ .idsᵉ .to-path-over h = fun-ext λ i → sb .idsᵉ .to-path-over (h i)

Extensional-∀
  : ∀ {ℓ ℓ′ ℓr} {A : Type ℓ} {B : A → Type ℓ′}
  → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
  → Extensional ∀[ B ] (ℓ ⊔ ℓr)
Extensional-∀ ⦃ sb ⦄ .Pathᵉ f g = ∀ {x} → Pathᵉ sb (f {x}) (g {x})
Extensional-∀ ⦃ sb ⦄ .reflᵉ f = reflᵉ sb f
Extensional-∀ ⦃ sb ⦄ .idsᵉ .to-path h i {x} = sb .idsᵉ .to-path (h {x}) i
Extensional-∀ ⦃ sb ⦄ .idsᵉ .to-path-over h i {x} = sb .idsᵉ .to-path-over (h {x}) i

Extensional-→
  : ∀ {ℓ ℓ′ ℓr} {A : Type ℓ} {B : Type ℓ′}
  → ⦃ sb : Extensional B ℓr ⦄
  → Extensional (A → B) (ℓ ⊔ ℓr)
Extensional-→ ⦃ sb ⦄ = Extensional-Π ⦃ λ {_} → sb ⦄

Extensional-uncurry
  : ∀ {ℓ ℓ′ ℓ″ ℓr} {A : Type ℓ} {B : A → Type ℓ′} {C : Type ℓ″}
  → ⦃ sb : Extensional ((x : A) → B x → C) ℓr ⦄
  → Extensional (Σ A B → C) ℓr
Extensional-uncurry ⦃ sb ⦄ .Pathᵉ f g = sb .Pathᵉ (curry² f) (curry² g)
Extensional-uncurry ⦃ sb ⦄ .reflᵉ f = sb .reflᵉ (curry² f)
Extensional-uncurry ⦃ sb = sb ⦄ .idsᵉ .to-path h i (a , b) = sb .idsᵉ .to-path h i a b
Extensional-uncurry ⦃ sb = sb ⦄ .idsᵉ .to-path-over h = sb .idsᵉ .to-path-over h

Extensional-×
  : ∀ {ℓ ℓ′ ℓr ℓs} {A : Type ℓ} {B : Type ℓ′}
  → ⦃ sa : Extensional A ℓr ⦄
  → ⦃ sb : Extensional B ℓs ⦄
  → Extensional (A × B) (ℓr ⊔ ℓs)
Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .Pathᵉ (x , y) (x′ , y′) = Pathᵉ sa x x′ × Pathᵉ sb y y′
Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .reflᵉ (x , y) = reflᵉ sa x , reflᵉ sb y
Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .idsᵉ .to-path (p , q) = ap² _,_
  (sa .idsᵉ .to-path p)
  (sb .idsᵉ .to-path q)
Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .idsᵉ .to-path-over (p , q) =
  Σ-pathP (sa .idsᵉ .to-path-over p) (sb .idsᵉ .to-path-over q)

Extensional-lift-map
  : ∀ {ℓ ℓ′ ℓ″ ℓr} {A : Type ℓ} {B : Type ℓ″}
  → ⦃ sa : Extensional (A → B) ℓr ⦄
  → Extensional (Lift ℓ′ A → B) ℓr
Extensional-lift-map ⦃ sa ⦄ .Pathᵉ f g = sa .Pathᵉ (f ∘ lift) (g ∘ lift)
Extensional-lift-map ⦃ sa ⦄ .reflᵉ x = sa .reflᵉ (x ∘ lift)
Extensional-lift-map ⦃ sa ⦄ .idsᵉ .to-path h i (lift x) = sa .idsᵉ .to-path h i x
Extensional-lift-map ⦃ sa ⦄ .idsᵉ .to-path-over h = sa .idsᵉ  .to-path-over h

@0 Extensional-Type : Extensional (Type ℓ) ℓ
Extensional-Type .Pathᵉ A B = A ≃ B
Extensional-Type .reflᵉ _ = idₑ
Extensional-Type .idsᵉ = univalence-identity-system

@0 Extensional-n-Type : ∀ {n} → Extensional (n-Type ℓ n) ℓ
Extensional-n-Type .Pathᵉ A B = Pathᵉ Extensional-Type ⌞ A ⌟ ⌞ B ⌟
Extensional-n-Type .reflᵉ _ = idₑ
Extensional-n-Type .idsᵉ .to-path = n-ua
Extensional-n-Type .idsᵉ .to-path-over = Extensional-Type .idsᵉ .to-path-over

instance
  extensionality-fun
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → Extensionality (A → B)
  extensionality-fun .Extensionality.lemma = quote Extensional-→

  extensionality-uncurry
    : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : A → Type ℓ′} {C : Type ℓ″}
    → Extensionality (Σ A B → C)
  extensionality-uncurry .Extensionality.lemma = quote Extensional-uncurry

  extensionality-lift-map
    : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ″}
    → Extensionality (Lift ℓ′ A → B)
  extensionality-lift-map .Extensionality.lemma = quote Extensional-lift-map

  extensionality-Π
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
    → Extensionality Π[ B ]
  extensionality-Π .Extensionality.lemma = quote Extensional-Π

  extensionality-∀
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
    → Extensionality ∀[ B ]
  extensionality-∀ .Extensionality.lemma = quote Extensional-∀

  extensionality-×
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → Extensionality (A × B)
  extensionality-× .Extensionality.lemma = quote Extensional-×

  extensionality-type : Extensionality (Type ℓ)
  extensionality-type .Extensionality.lemma = quote Extensional-Type

  extensionality-n-type : ∀ {n} → Extensionality (n-Type ℓ n)
  extensionality-n-type .Extensionality.lemma = quote Extensional-n-Type

{-
Actual user-facing entry point for the tactic: using the 'extensional'
tactic (through the blanket instance) we can find an identity system for
the type A, and turn a proof in the computed relation to an identity.
-}
ext
  : ∀ {ℓ ℓr} {A : Type ℓ} ⦃ r : Extensional A ℓr ⦄ {x y : A}
  → Pathᵉ r x y → x ＝ y
ext ⦃ r ⦄ p = r .idsᵉ .to-path p

{-
Using the extensionality tactic we can define a "more general refl",
where the terms being compared are not definitionally equal, but they
inhabit a type with a good identity system for which 'r x : R x y' type
checks.

The idea is to write a function wrapping

  ext : ⦃ r : Extensional A ℓ ⦄ (p : Pathᵉ r x y) → x ≡ y

so that it gives (reflᵉ r x) as the default argument for p. We can use a
tactic argument to accomplish this.
-}

private
  trivial-worker
    : ∀ {ℓ ℓr} {A : Type ℓ}
    → (r : Extensional A ℓr)
    → (x y : A)
    → Term
    → TC ⊤
  trivial-worker r x y goal = try where
    error : ∀ {ℓ} {A : Type ℓ} → TC A

    -- We already have our r : Extensional A ℓr, and this is a macro, so
    -- we can just check that r .reflᵉ x : R x y. If that's the case
    -- then we can use that as the argument, otherwise we can give a
    -- slightly better error message than what Agda would yell.
    try : TC ⊤
    try = do
      `r ← wait-for-type =<< quoteωTC r
      ty ← quoteTC (Pathᵉ r x y)
      `x ← quoteTC x
      `refl ← check-type (it reflᵉ ##ₙ `r ##ₙ `x) ty <|> error
      unify goal `refl

    error = do
      `x ← quoteTC x
      `y ← quoteTC y
      type-error
        [ "trivial! failed: the values\n  "
        , termErr `x , "\nand\n  " , termErr `y
        , "\nare not extensionally equal by refl." ]

{-
trivial! serves to replace proofs like

  Nat-path λ x → funext λ y → Nat-path λ z → Homomorphism-path λ a → refl

since this is

  ext λ x y z a → refl

and that argument is precisely reflexivity for the computed identity
system which 'ext' is using. By the way, this example is totally made
up.
-}

opaque
  trivial!
    : ∀ {ℓ ℓr} {A : Type ℓ} {x y : A}
    → ⦃ r : Extensional A ℓr ⦄
    → {@(tactic trivial-worker r x y) p : Pathᵉ r x y}
    → x ＝ y
  trivial! ⦃ r ⦄ {p} = r .idsᵉ .to-path p

  unext : ∀ {ℓ ℓr} {A : Type ℓ} ⦃ e : Extensional A ℓr ⦄ {x y : A} → x ＝ y → e .Pathᵉ x y
  unext ⦃ e ⦄ {x = x} p = transport (λ i → e .Pathᵉ x (p i)) (e .reflᵉ x)

macro
  reext!
    : ∀ {ℓ ℓr} {A : Type ℓ} ⦃ ea : Extensional A ℓr ⦄ {x y : A}
    → x ＝ y → Term → TC ⊤
  reext! p goal = do
    `p ← quoteTC p
    unify goal (def (quote ext) [ argN (def (quote unext) [ argN `p ]) ])

Pathᵉ-is-of-hlevel
  : ∀ {ℓ ℓr} {A : Type ℓ} n (sa : Extensional A ℓr)
  → is-of-hlevel (suc n) A
  → ∀ {x y}
  → is-of-hlevel n (Pathᵉ sa x y)
Pathᵉ-is-of-hlevel n sa hl =
  is-of-hlevel-≃ _ (identity-system-gives-path (sa .idsᵉ))
    ((path-is-of-hlevel′ _ hl _ _))
