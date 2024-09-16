{-# OPTIONS --safe #-}
module Data.Reflects.Base where

open import Foundations.Prelude

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Unit.Base as ⊤

data Reflects⁰ {ℓ} (P : Type ℓ) : Bool → Type ℓ where
  ofʸ : ( p :   P) → Reflects⁰ P true
  ofⁿ : (¬p : ¬ P) → Reflects⁰ P false

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ ℓᶜ : Level
  a b : Bool
  P : Type ℓ
  Q : Type ℓ′

instance
  Reflectance-Underlying
    : {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Reflectance A Bool
  Reflectance-Underlying ⦃ ua ⦄ .ℓ-reflectance = ua .Underlying.ℓ-underlying
  Reflectance-Underlying .Reflects X = Reflects⁰ ⌞ X ⌟
  {-# OVERLAPPABLE Reflectance-Underlying #-}

  Refl-Reflects
    : {A : Type ℓᵃ} {R : A → A → Type ℓ}
      ⦃ r : Refl R ⦄
    → Refl (λ a b → Reflects (R a b) true)
  Refl-Reflects .refl = ofʸ refl

  Comp-Reflects
    : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
      {L : A → B → Type ℓ} {R : B → C → Type ℓ′} {O : A → C → Type ℓ″}
      ⦃ t : Comp L R O ⦄
    → Comp (λ a b → Reflects (L a b) true) (λ a b → Reflects (R a b) true) (λ a b → Reflects (O a b) true)
  Comp-Reflects ._∙_ (ofʸ p) (ofʸ q) = ofʸ (p ∙ q)

  Reflects-Lift : ⦃ Reflects P b ⦄ → Reflects (Lift ℓ′ P) b
  Reflects-Lift {b = false} ⦃ ofⁿ ¬p ⦄ = ofⁿ (¬p ∘ lower)
  Reflects-Lift {b = true}  ⦃ ofʸ  p ⦄ = ofʸ (lift p)

  Reflects-So : Reflects (So b) b
  Reflects-So {(false)} = ofⁿ λ ()
  Reflects-So {(true)}  = ofʸ oh

  Reflects-refl : {x : P} → Reflects (x ＝ x) true
  Reflects-refl = ofʸ refl
  {-# INCOHERENT Reflects-refl #-}

  Reflects-⊥ : Reflects ⊥ false
  Reflects-⊥ = ofⁿ refl

  Reflects-⊤ : Reflects ⊤ true
  Reflects-⊤ = ofʸ tt

  Reflects-¬ : ⦃ rp : Reflects P a ⦄ → Reflects (¬ P) (not a)
  Reflects-¬ {a = false} ⦃ ofⁿ  p ⦄ = ofʸ p
  Reflects-¬ {a = true}  ⦃ ofʸ ¬p ⦄ = ofⁿ (_$ ¬p)
  {-# INCOHERENT Reflects-¬ #-}

  Reflects-× : ⦃ rp : Reflects P a ⦄ ⦃ rq : Reflects Q b ⦄ → Reflects (P × Q) (a and b)
  Reflects-× {a = false} {b}         ⦃ ofⁿ ¬p ⦄            = ofⁿ (¬p ∘ fst)
  Reflects-× {a = true}  {b = false} ⦃ ofʸ  p ⦄ ⦃ ofⁿ ¬q ⦄ = ofⁿ (¬q ∘ snd)
  Reflects-× {a = true}  {b = true}  ⦃ ofʸ  p ⦄ ⦃ ofʸ  q ⦄ = ofʸ (p , q)

  Reflects-⇒ : ⦃ rp : Reflects P a ⦄ ⦃ rq : Reflects Q b ⦄ → Reflects (P ⇒ Q) (a implies b)
  Reflects-⇒ {a = true}  {b = false} ⦃ ofʸ  p ⦄ ⦃ ofⁿ ¬q ⦄ = ofⁿ (¬q ∘ (_$ p))
  Reflects-⇒ {a = true}  {b = true}  ⦃ ofʸ  p ⦄ ⦃ ofʸ  q ⦄ = ofʸ (λ _ → q)
  Reflects-⇒ {a = false}             ⦃ ofⁿ ¬p ⦄            = ofʸ (λ p → ⊥.rec (¬p p))

so→true! : ⦃ Reflects P a ⦄ → ⌞ a ⌟ → P
so→true! ⦃ ofʸ p ⦄ oh = p

so→falseᴱ! : ⦃ _ : Reflects P a ⦄ (@0 _ : ⌞ not a ⌟) → @0 P → Q
so→falseᴱ! ⦃ ofⁿ ¬p ⦄ oh p = ⊥.rec (¬p p)

so→false! : ⦃ Reflects P a ⦄ → ⌞ not a ⌟ → P → Q
so→false! n p = so→falseᴱ! n p

true→so! : ⦃ Reflects P a ⦄ → P → ⌞ a ⌟
true→so! ⦃ ofʸ  p ⦄ _ = oh
true→so! ⦃ ofⁿ ¬p ⦄ p = ⊥.rec (¬p p)

false→soᴱ! : ⦃ _ : Reflects P a ⦄ (@0 _ : ¬ P) → ⌞ not a ⌟
false→soᴱ! ⦃ ofʸ  p ⦄ ¬p = ⊥.rec (¬p p)
false→soᴱ! ⦃ ofⁿ ¬p ⦄ _  = oh

false→so! : ⦃ Reflects P a ⦄ → ¬ P → ⌞ not a ⌟
false→so! ¬p = false→soᴱ! ¬p

true! : ⦃ Reflects P true ⦄ → P
true! = so→true! oh

falseᴱ! : ⦃ Reflects P false ⦄ → @0 P → Q
falseᴱ! p = ⊥.rec (so→false! oh p)

false! : ⦃ Reflects P false ⦄ → P → Q
false! p = falseᴱ! p

reflects-not : Reflects (¬ ⌞ a ⌟) (not a)
reflects-not = auto

reflects-and : Reflects (⌞ a ⌟ × ⌞ b ⌟) (a and b)
reflects-and = auto

of : if b then P else ¬ P → Reflects P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : Reflects P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

dmap : (P → Q) → (¬ P → ¬ Q) → Reflects P b → Reflects Q b
dmap to fro (ofʸ  p) = ofʸ (to p)
dmap to fro (ofⁿ ¬p) = ofⁿ (fro ¬p)

reflects-sym : {x y : P} → Reflects (x ＝ y) b → Reflects (y ＝ x) b
reflects-sym = dmap sym (contra sym)


module _ {A : Type ℓ} {_==_ : A → A → Bool} ⦃ re : ∀ {x y : A} → Reflects (x ＝ y) (x == y) ⦄ where
  reflects-path→identity-system! : is-identity-system (λ x y → ⌞ x == y ⌟) (λ a → true→so! ⦃ re {a} {a} ⦄ refl)
  reflects-path→identity-system! = set-identity-system! (so→true! ⦃ re ⦄)

  opaque
    reflects-path→is-set! : is-set A
    reflects-path→is-set! = identity-system→is-of-hlevel! 1 reflects-path→identity-system!
