{-# OPTIONS --safe #-}
module Meta.Extensionality where

open import Foundations.Prelude
  hiding (_$_)

open import Meta.Effect.Alt
open import Meta.Literals.FromProduct
open import Meta.Reflection.Base
open import Meta.Reflection.Neutral
open import Meta.Reflection.Signature
open import Meta.Reflection.Subst
open import Meta.Variadic

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Maybe.Instances.Alt
open import Data.Reflection.Error
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Term


record Extensional {ℓ} (A : Type ℓ) (ℓ-rel : Level) : Type (ℓ ⊔ ℓsuc ℓ-rel) where
  no-eta-equality
  field
    Pathᵉ : A → A → Type ℓ-rel
    reflᵉ : ∀ x → Pathᵉ x x
    idsᵉ  : is-identity-system Pathᵉ reflᵉ

open Extensional using (Pathᵉ ; reflᵉ ; idsᵉ) public

private variable ℓ ℓ′ : Level

J!
  : ∀{ℓ ℓr ℓ″} {A : Type ℓ} {x : A}
  → ⦃ sa : Extensional A ℓr ⦄
  → (P : ∀ b → sa .Pathᵉ x b → Type ℓ″)
  → (d : P x (sa .reflᵉ x))
  → ∀ {b} s → P b s
J! ⦃ sa ⦄ P d _ = IdS.J (sa .idsᵉ) P d _

infix 10 J>!_
J>!_
  : ∀{ℓ ℓr ℓ″} {A : Type ℓ} {x : A}
  → ⦃ sa : Extensional A ℓr ⦄
  → {P : ∀ b → sa .Pathᵉ x b → Type ℓ″}
  → P x (sa .reflᵉ x)
  → ∀ b s → P b s
J>!_ {P} b _ = J! P b

instance
  -- Default instance, uses regular paths for the relation.
  Extensional-default : {A : Type ℓ} → Extensional A ℓ
  Extensional-default .Pathᵉ   = _＝_
  Extensional-default .reflᵉ _ = refl
  Extensional-default .idsᵉ    = path-identity-system
  {-# INCOHERENT Extensional-default #-}

  Extensional-Lift
    : ∀ {ℓr} {A : Type ℓ}
    → ⦃ sa : Extensional A ℓr ⦄
    → Extensional (Lift ℓ′ A) ℓr
  Extensional-Lift ⦃ sa ⦄ .Pathᵉ (lift x) (lift y) = sa .Pathᵉ x y
  Extensional-Lift ⦃ sa ⦄ .reflᵉ (lift x) = sa .reflᵉ x
  Extensional-Lift ⦃ sa ⦄ .idsᵉ .to-path p = ap lift (sa .idsᵉ .to-path p)
  Extensional-Lift ⦃ sa ⦄ .idsᵉ .to-path-over p = sa .idsᵉ .to-path-over p

  Extensional-Π
    : ∀ {ℓ ℓ′ ℓr} {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
    → Extensional Π[ B ] (ℓ ⊔ ℓr)
  Extensional-Π ⦃ sb ⦄ .Pathᵉ f g = ∀ x → Pathᵉ sb (f x) (g x)
  Extensional-Π ⦃ sb ⦄ .reflᵉ f x = reflᵉ sb (f x)
  Extensional-Π ⦃ sb ⦄ .idsᵉ .to-path h = fun-ext λ i → sb .idsᵉ .to-path (h i)
  Extensional-Π ⦃ sb ⦄ .idsᵉ .to-path-over h = fun-ext λ i → sb .idsᵉ .to-path-over (h i)
  {-# OVERLAPPABLE Extensional-Π #-}

  Extensional-∀
    : ∀ {ℓ ℓ′ ℓr} {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
    → Extensional ∀[ B ] (ℓ ⊔ ℓr)
  Extensional-∀ ⦃ sb ⦄ .Pathᵉ f g = ∀ {x} → Pathᵉ sb (f {x}) (g {x})
  Extensional-∀ ⦃ sb ⦄ .reflᵉ f = reflᵉ sb f
  Extensional-∀ ⦃ sb ⦄ .idsᵉ .to-path h i {x} = sb .idsᵉ .to-path (h {x}) i
  Extensional-∀ ⦃ sb ⦄ .idsᵉ .to-path-over h i {x} = sb .idsᵉ .to-path-over (h {x}) i

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
    sa .idsᵉ .to-path-over p ,ₚ sb .idsᵉ .to-path-over q
  {-# OVERLAPPABLE Extensional-× #-}

  Extensional-lift-map
    : ∀ {ℓ ℓ′ ℓ″ ℓr} {A : Type ℓ} {B : Lift ℓ′ A → Type ℓ″}
    → ⦃ sa : Extensional ((x : A) → B (lift x)) ℓr ⦄
    → Extensional ((x : Lift ℓ′ A) → B x) ℓr
  Extensional-lift-map ⦃ sa ⦄ .Pathᵉ f g = sa .Pathᵉ (f ∘ lift) (g ∘ lift)
  Extensional-lift-map ⦃ sa ⦄ .reflᵉ x = sa .reflᵉ (x ∘ lift)
  Extensional-lift-map ⦃ sa ⦄ .idsᵉ .to-path h i (lift x) = sa .idsᵉ .to-path h i x
  Extensional-lift-map ⦃ sa ⦄ .idsᵉ .to-path-over h = sa .idsᵉ  .to-path-over h

  @0 Extensional-Type : Extensional (Type ℓ) ℓ
  Extensional-Type .Pathᵉ A B = A ≃ B
  Extensional-Type .reflᵉ _ = refl
  Extensional-Type .idsᵉ = univalence-identity-system


ext
  : ∀ {ℓ ℓr} {A : Type ℓ} {x y : A} ⦃ r : Extensional A ℓr ⦄
  → Pathᵉ r x y → x ＝ y
ext ⦃ r ⦄ p = r .idsᵉ .to-path p

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
      `r ← wait-for-type =<< quoteTC r
      `x ← quoteTC x
      unify goal (it reflᵉ ##ₙ `r ##ₙ `x) <|> error

    error = do
      `x ← quoteTC x
      `y ← quoteTC y
      type-error
        [ "trivial! failed: the values\n  "
        , term-err `x , "\nand\n  " , term-err `y
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

trivial-iso!
  : ∀ {ℓ ℓ′ ℓr ℓs} {A : Type ℓ} {B : Type ℓ′}
  → ⦃ r : Extensional (A → A) ℓr ⦄
  → ⦃ s : Extensional (B → B) ℓs ⦄
  → (f : A → B)
  → (g : B → A)
  → {@(tactic trivial-worker r (g ∘ f) id) p : Pathᵉ r (g ∘ f) id}
  → {@(tactic trivial-worker s (f ∘ g) id) q : Pathᵉ s (f ∘ g) id}
  → Iso A B
trivial-iso! ⦃ r ⦄ ⦃ s ⦄ f g {p} {q} =
  f , iso g (s .idsᵉ .to-path q $ₚ_) (r .idsᵉ .to-path p $ₚ_)

macro
  reext!
    : ∀ {ℓ ℓr} {A : Type ℓ} ⦃ ea : Extensional A ℓr ⦄ {x y : A}
    → x ＝ y → Term → TC ⊤
  reext! p goal = do
    `p ← quoteTC p
    unify goal $ it ext ##ₙ (it unext ##ₙ `p)

Pathᵉ-is-of-hlevel
  : ∀ {ℓ ℓr} {A : Type ℓ} n (sa : Extensional A ℓr)
  → is-of-hlevel (suc n) A
  → ∀ {x y}
  → is-of-hlevel n (Pathᵉ sa x y)
Pathᵉ-is-of-hlevel n sa hl =
  ≃→is-of-hlevel n (identity-system-gives-path (sa .idsᵉ))
    ((path-is-of-hlevel n hl _ _))
