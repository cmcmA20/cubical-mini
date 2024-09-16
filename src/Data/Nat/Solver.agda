{-# OPTIONS --safe --no-exact-split #-}
module Data.Nat.Solver where

open import Foundations.Base
  hiding (const)

open import Meta.Effect.Idiom
open import Meta.Literals.FromNat
open import Meta.Marker
open import Meta.Reflection.Base
open import Meta.Reflection.Solver
open import Meta.Reflection.Variables

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.List.Instances.FromProduct
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Instances.FromNat
open import Data.Nat.Properties
open import Data.Reflection.Argument
open import Data.Reflection.Term
open import Data.Unit.Base
open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Operations.Computational

private variable
  ℓᵃ : Level
  A : Type ℓᵃ
  n : ℕ

data Poly {ℓᵃ} (A : Type ℓᵃ) : ℕ → Type ℓᵃ where
  const : (c : A) → Poly A 0
  zerop : ∀ {n} → Poly A (suc n)
  _*X+_ : ∀ {n} (p : Poly A (suc n)) (q : Poly A n) → Poly A (suc n)

infixl 2 _*X+_

commute-inner : ∀ w x y z → (w + x) + (y + z) ＝ (w + y) + (x + z)
commute-inner w x y z =
  (w + x) + (y + z)    ~⟨ +-assoc w _ _ ⟨
  w + ⌜ x + (y + z) ⌝  ~⟨ ap! (+-assoc x _ _) ⟩
  w + (⌜ x + y ⌝ + z)  ~⟨ ap! (+-comm x _) ⟩
  w + ⌜ y + x + z ⌝    ~⟨ ap¡ (+-assoc y _ _) ⟨
  w + (y + (x + z))    ~⟨ +-assoc w _ _ ⟩
  (w + y) + (x + z)    ∎

commute-last : ∀ x y z → (x · y) · z ＝ (x · z) · y
commute-last x y z =
  x · y · z      ~⟨ ·-assoc x y z ⟨
  x · ⌜ y · z ⌝  ~⟨ ap! (·-comm y z) ⟩
  x · (z · y)    ~⟨ ·-assoc x z y ⟩
  x · z · y      ∎

private
  x⁴+1 : Poly ℕ 1
  x⁴+1 = zerop *X+ const 1 *X+ const 0 *X+ const 0 *X+ const 0 *X+ const 0

0ₚ : Poly ℕ n
0ₚ {0}     = const zero
0ₚ {suc _} = zerop

constₚ : ℕ → Poly ℕ n
constₚ {0}     = const
constₚ {suc n} c = 0ₚ *X+ constₚ c

1ₚ : Poly ℕ n
1ₚ = constₚ 1

X[_] : Fin n → Poly ℕ n
X[_] {suc _} (mk-fin 0)             = 1ₚ *X+ 0ₚ
X[_] {suc _} (mk-fin (suc k) {(b)}) = 0ₚ *X+ X[ mk-fin k {b} ]

infixl 6 _+ₚ_
infixl 7 _*ₚ_

_+ₚ_ : Poly ℕ n → Poly ℕ n → Poly ℕ n
const c₁ +ₚ const c₂ = const (c₁ + c₂)
zerop     +ₚ q         = q
(p *X+ q) +ₚ zerop     = p *X+ q
(p *X+ r) +ₚ (q *X+ s) = (p +ₚ q) *X+ (r +ₚ s)

_*ₚ_ : Poly ℕ n → Poly ℕ n → Poly ℕ n
_*ₚ′_ : Poly ℕ n → Poly ℕ (suc n) → Poly ℕ (suc n)

const c₁  *ₚ const c₂ = const (c₁ · c₂)
zerop     *ₚ q        = zerop
(p *X+ q) *ₚ r        = ((p *ₚ r) *X+ 0ₚ) +ₚ (q *ₚ′ r)

r *ₚ′ zerop     = zerop
r *ₚ′ (p *X+ q) = (r *ₚ′ p) *X+ (r *ₚ q)

⟦_⟧ₚ : Poly ℕ n → Vec ℕ n → ℕ
⟦ const c ⟧ₚ _          = c
⟦ zerop ⟧ₚ   _          = 0
⟦ p *X+ q ⟧ₚ (x₀ ∷ env) = ⟦ p ⟧ₚ (x₀ ∷ env) · x₀ + ⟦ q ⟧ₚ env

sound-0ₚ : (env : Vec ℕ n) → ⟦ 0ₚ ⟧ₚ env ＝ 0
sound-0ₚ {0}     _ = refl
sound-0ₚ {suc n} _ = refl


sound-constₚ : ∀ c → (env : Vec ℕ n) → ⟦ constₚ c ⟧ₚ env ＝ c
sound-constₚ {0}     _ _         = refl
sound-constₚ {suc n} c (x ∷ env) = sound-constₚ c env

sound-X[_] : ∀ k → (env : Vec ℕ n) → ⟦ X[ k ] ⟧ₚ env ＝ lookup env k
sound-X[_] {suc _} (mk-fin 0) (x₀ ∷ env) =
  ⌜ ⟦ constₚ 1 ⟧ₚ env ⌝ · x₀ + ⟦ 0ₚ ⟧ₚ env  ~⟨ ap! (sound-constₚ 1 env) ⟩
  1 · x₀ + ⌜ ⟦ 0ₚ ⟧ₚ env ⌝                  ~⟨ ap! (sound-0ₚ env) ⟩
  1 · x₀ + 0                                ~⟨ +-zero-r (1 · x₀) ⟩
  1 · x₀                                    ~⟨ ·-id-l x₀ ⟩
  x₀                                        ∎
sound-X[_] {suc _} (mk-fin (suc k)) (_ ∷ env) = sound-X[ mk-fin k ] env

sound-+ₚ : ∀ p q → (env : Vec ℕ n)
         → ⟦ p +ₚ q ⟧ₚ env ＝ ⟦ p ⟧ₚ env + ⟦ q ⟧ₚ env
sound-+ₚ (const _) (const _) _   = refl
sound-+ₚ zerop     _         _   = refl
sound-+ₚ (p *X+ r) zerop     env = sym $ +-zero-r $
  ⟦ (p *X+ r) +ₚ zerop ⟧ₚ env
sound-+ₚ (p *X+ r) (q *X+ s) (x₀ ∷ env) =
  ⌜ ⟦p+q⟧ ⌝ · x₀ + ⟦r+s⟧              ~⟨ ap! (sound-+ₚ p _ _) ⟩
  (⟦p⟧ + ⟦q⟧) · x₀ + ⌜ ⟦r+s⟧ ⌝        ~⟨ ap! (sound-+ₚ r _ _) ⟩
  ⌜ (⟦p⟧ + ⟦q⟧) · x₀ ⌝ + (⟦r⟧ + ⟦s⟧)  ~⟨ ap! (·-distrib-+-r ⟦p⟧ ⟦q⟧ x₀) ⟩
  ⟦p⟧ · x₀ + ⟦q⟧ · x₀ + (⟦r⟧ + ⟦s⟧)   ~⟨ commute-inner (⟦p⟧ · x₀) (⟦q⟧ · x₀) ⟦r⟧ ⟦s⟧ ⟩
  ⟦p⟧ · x₀ + ⟦r⟧ + (⟦q⟧ · x₀ + ⟦s⟧)   ∎
  where
    ⟦p+q⟧ = ⟦ p +ₚ q ⟧ₚ (x₀ ∷ env)
    ⟦r+s⟧ = ⟦ r +ₚ s ⟧ₚ env
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦r⟧ = ⟦ r ⟧ₚ env
    ⟦q⟧ = ⟦ q ⟧ₚ (x₀ ∷ env)
    ⟦s⟧ = ⟦ s ⟧ₚ env

sound-*ₚ
  : ∀ p q → (env : Vec ℕ n)
  → ⟦ p *ₚ q ⟧ₚ env ＝ ⟦ p ⟧ₚ env · ⟦ q ⟧ₚ env
sound-*ₚ′
  : ∀ p q → (x₀ : ℕ) → (env : Vec ℕ n)
  → ⟦ p *ₚ′ q ⟧ₚ (x₀ ∷ env) ＝ ⟦ p ⟧ₚ env · ⟦ q ⟧ₚ (x₀ ∷ env)

sound-*ₚ (const _) (const _) _ = refl
sound-*ₚ zerop _ _ = refl
sound-*ₚ (p *X+ r) zerop (x₀ ∷ env) =
  ⌜ ⟦ p *ₚ zerop ⟧ₚ (x₀ ∷ env) ⌝ · x₀ + ⟦ 0ₚ ⟧ₚ env  ~⟨ ap! (sound-*ₚ p _ _) ⟩
  ⟦p⟧ · 0 · x₀ + ⌜ ⟦ 0ₚ ⟧ₚ env ⌝                     ~⟨ ap! (sound-0ₚ env) ⟩
  ⌜ ⟦p⟧ · 0 ⌝ · x₀ + 0                               ~⟨ ap! (·-absorb-r ⟦p⟧) ⟩
  0                                                  ~⟨ ·-absorb-r (⟦p⟧ · x₀ + ⟦r⟧) ⟨
  (⟦p⟧ · x₀ + ⟦r⟧) · 0                               ∎
  where
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦r⟧ = ⟦ r ⟧ₚ env

sound-*ₚ (p *X+ r) (q *X+ s) (x₀ ∷ env) =
  ⟦p*⟨qx+s⟩+r*q⟧ · x₀ + ⌜ ⟦ 0ₚ +ₚ (r *ₚ s) ⟧ₚ env ⌝               ~⟨ ap! (sound-+ₚ 0ₚ (r *ₚ s) _) ⟩
  ⟦p*⟨qx+s⟩+r*q⟧ · x₀ + (⌜ ⟦ 0ₚ ⟧ₚ env ⌝ + ⟦ r *ₚ s ⟧ₚ env)       ~⟨ ap! (sound-0ₚ env) ⟩
  ⟦p*⟨qx+s⟩+r*q⟧ · x₀ + ⌜ ⟦ r *ₚ s ⟧ₚ env ⌝                       ~⟨ ap! (sound-*ₚ r _ _) ⟩
  ⌜ ⟦p*⟨qx+s⟩+r*q⟧ ⌝ · x₀ + ⟦r⟧ · ⟦s⟧                             ~⟨ ap! (sound-+ₚ (p *ₚ (q *X+ s)) (r *ₚ′ q) _) ⟩
  (⌜ ⟦p*⟨qx+s⟩⟧ ⌝ + ⟦r*q⟧) · x₀ + ⟦r⟧ · ⟦s⟧                       ~⟨ ap! (sound-*ₚ p _ _) ⟩
  (⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) + ⌜ ⟦r*q⟧ ⌝) · x₀ + ⟦r⟧ · ⟦s⟧           ~⟨ ap! (sound-*ₚ′ r q _ _) ⟩
  ⌜ (⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) + ⟦r⟧ · ⟦q⟧) · x₀ ⌝ + ⟦r⟧ · ⟦s⟧       ~⟨ ap! (·-distrib-+-r (⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧)) (⟦r⟧ · ⟦q⟧) x₀) ⟩
  ⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) · x₀ + ⟦r⟧ · ⟦q⟧ · x₀ + ⟦r⟧ · ⟦s⟧        ~⟨ +-assoc (⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) · x₀) _ _ ⟨
  ⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) · x₀ + (⌜ ⟦r⟧ · ⟦q⟧ · x₀ ⌝ + ⟦r⟧ · ⟦s⟧)  ~⟨ ap¡ (·-assoc ⟦r⟧ _ _) ⟨
  ⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) · x₀ + ⌜ ⟦r⟧ · (⟦q⟧ · x₀) + ⟦r⟧ · ⟦s⟧ ⌝  ~⟨ ap¡ (·-distrib-+-l ⟦r⟧ _ _) ⟨
  ⌜ ⟦p⟧ · (⟦q⟧ · x₀ + ⟦s⟧) · x₀ ⌝ + ⟦r⟧ · (⟦q⟧ · x₀ + ⟦s⟧)        ~⟨ ap! (commute-last ⟦p⟧ _ _) ⟩
  ⟦p⟧ · x₀ · (⟦q⟧ · x₀ + ⟦s⟧) + ⟦r⟧ · (⟦q⟧ · x₀ + ⟦s⟧)            ~⟨ ·-distrib-+-r (⟦p⟧ · x₀) _ _ ⟨
  (⟦p⟧ · x₀ + ⟦r⟧) · (⟦q⟧ · x₀ + ⟦s⟧)                             ∎
  where
    ⟦p*⟨qx+s⟩+r*q⟧ = ⟦ (p *ₚ (q *X+ s)) +ₚ (r *ₚ′ q) ⟧ₚ (x₀ ∷ env)
    ⟦p*⟨qx+s⟩⟧ = ⟦ p *ₚ (q *X+ s) ⟧ₚ (x₀ ∷ env)
    ⟦r*q⟧ = ⟦ r *ₚ′ q ⟧ₚ (x₀ ∷ env)
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦r⟧ = ⟦ r ⟧ₚ env
    ⟦q⟧ = ⟦ q ⟧ₚ (x₀ ∷ env)
    ⟦s⟧ = ⟦ s ⟧ₚ env

sound-*ₚ′ p zerop x₀ env = sym (·-absorb-r (⟦ p ⟧ₚ env))
sound-*ₚ′ r (p *X+ q) x₀ env =
  ⌜ ⟦ r *ₚ′ p ⟧ₚ (x₀ ∷ env) ⌝ · x₀ + ⟦ r *ₚ q ⟧ₚ env  ~⟨ ap! (sound-*ₚ′ r p _ _) ⟩
  ⟦r⟧ · ⟦p⟧ · x₀ + ⌜ ⟦ r *ₚ q ⟧ₚ env ⌝                ~⟨ ap! (sound-*ₚ r _ _) ⟩
  ⌜ ⟦r⟧ · ⟦p⟧ · x₀ ⌝ + ⟦r⟧ · ⟦q⟧                      ~⟨ ap¡ (·-assoc ⟦r⟧ _ _) ⟨
  ⟦r⟧ · (⟦p⟧ · x₀) + ⟦r⟧ · ⟦q⟧                        ~⟨ ·-distrib-+-l ⟦r⟧ _ _ ⟨
  ⟦r⟧ · (⟦p⟧ · x₀ + ⟦q⟧)                              ∎
  where
    ⟦r⟧ = ⟦ r ⟧ₚ env
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦q⟧ = ⟦ q ⟧ₚ env


data Expr : ℕ → Type where
  ‵0   : Expr n
  ‵lit : ℕ     → Expr n
  ‵_   : Fin n → Expr n
  ‵1+_ : Expr n → Expr n
  _‵+_ : Expr n → Expr n → Expr n
  _‵·_ : Expr n → Expr n → Expr n

⟦_⟧ₑ : Expr n → Vec ℕ n → ℕ
⟦ ‵ k      ⟧ₑ env = lookup env k
⟦ ‵0       ⟧ₑ _   = 0
⟦ ‵1+ e    ⟧ₑ env = suc (⟦ e ⟧ₑ env)
⟦ ‵lit k   ⟧ₑ _   = k
⟦ e₁ ‵+ e₂ ⟧ₑ env = ⟦ e₁ ⟧ₑ env + ⟦ e₂ ⟧ₑ env
⟦ e₁ ‵· e₂ ⟧ₑ env = ⟦ e₁ ⟧ₑ env · ⟦ e₂ ⟧ₑ env

↓_ : Expr n → Poly ℕ n
↓ (‵ k)      = X[ k ]
↓ ‵0         = 0ₚ
↓ (‵1+ e)    = constₚ 1 +ₚ ↓ e
↓ ‵lit k     = constₚ k
↓ (e₁ ‵+ e₂) = (↓ e₁) +ₚ (↓ e₂)
↓ (e₁ ‵· e₂) = (↓ e₁) *ₚ (↓ e₂)

sound : ∀ e → (env : Vec ℕ n) → ⟦ ↓ e ⟧ₚ env ＝ ⟦ e ⟧ₑ env
sound (‵ k) env = sound-X[ k ] env
sound ‵0 env = sound-0ₚ env
sound (‵1+ e) env =
  ⟦ constₚ 1 +ₚ (↓ e) ⟧ₚ env            ~⟨ sound-+ₚ (constₚ 1) (↓ e) env ⟩
  ⌜ ⟦ constₚ 1 ⟧ₚ env ⌝ + ⟦ ↓ e ⟧ₚ env  ~⟨ ap! (sound-constₚ 1 env) ⟩
  suc (⟦ ↓ e ⟧ₚ env)                    ~⟨ ap suc (sound e env) ⟩
  suc (⟦ e ⟧ₑ env)                      ∎
sound (‵lit k) env = sound-constₚ k env
sound (e₁ ‵+ e₂) env =
  ⟦ (↓ e₁) +ₚ (↓ e₂) ⟧ₚ env      ~⟨ sound-+ₚ (↓ e₁) (↓ e₂) env ⟩
  ⟦ ↓ e₁ ⟧ₚ env + ⟦ ↓ e₂ ⟧ₚ env  ~⟨ ap² _+_ (sound e₁ env) (sound e₂ env) ⟩
  ⟦ e₁ ⟧ₑ env + ⟦ e₂ ⟧ₑ env      ∎
sound (e₁ ‵· e₂) env =
  ⟦ (↓ e₁) *ₚ (↓ e₂) ⟧ₚ env      ~⟨ sound-*ₚ (↓ e₁) (↓ e₂) env ⟩
  ⟦ ↓ e₁ ⟧ₚ env · ⟦ ↓ e₂ ⟧ₚ env  ~⟨ ap² _·_ (sound e₁ env) (sound e₂ env) ⟩
  ⟦ e₁ ⟧ₑ env · ⟦ e₂ ⟧ₑ env      ∎

expand : (e : Expr n) (env : Vec ℕ n) → ℕ
expand e = ⟦ ↓ e ⟧ₚ

opaque
  solve : ∀ e₁ e₂ (env : Vec ℕ n)
        → expand e₁ env ＝ expand e₂ env
        → ⟦ e₁ ⟧ₑ env   ＝ ⟦ e₂ ⟧ₑ env
  solve e₁ e₂ env p = sym (sound e₁ env) ∙∙ p ∙∙ sound e₂ env


-- Reflection

private
  pattern “zero” =
    con (quote zero) []
  pattern “suc” x =
    con (quote suc) (x v∷ [])
  pattern _“+”_ x y =
    def (quote _+_) (x v∷ y v∷ _)
  pattern _“·”_ x y =
    def (quote _·_) (x v∷ y v∷ _)

  build-expr : Variables ℕ → Term → TC (Term × Variables ℕ)
  build-expr vs (nat-lit n) = do
    ‵n ← quoteTC n
    pure $ con (quote ‵lit) (‵n v∷ []) , vs
  build-expr vs “zero” = do
    pure $ con (quote ‵0) (unknown h∷ []) , vs
  build-expr vs (“suc” t) = do
    e , vs ← build-expr vs t
    pure $ con (quote ‵1+_) (unknown h∷ e v∷ []) , vs
  build-expr vs (t₁ “+” t₂) = do
    e₁ , vs ← build-expr vs t₁
    e₂ , vs ← build-expr vs t₂
    pure $ con (quote _‵+_) (unknown h∷ e₁ v∷ e₂ v∷ []) , vs
  build-expr vs (t₁ “·” t₂) = do
    e₁ , vs ← build-expr vs t₁
    e₂ , vs ← build-expr vs t₂
    pure $ con (quote _‵·_) (unknown h∷ e₁ v∷ e₂ v∷ []) , vs
  build-expr vs (def (quote ⌜_⌝) (_ h∷ _ h∷ tm v∷ [])) =
    build-expr vs tm -- dirty!
  build-expr vs tm = do
    (v , vs′) ← bind-var vs tm
    pure $ con (quote ‵_) (v v∷ []) , vs′

  “expand” : Term → Term → Term
  “expand” e env = def (quote expand) (unknown h∷ e v∷ env v∷ [])

  “solve” : Term → Term → Term → Term
  “solve” lhs rhs env =
    def (quote solve)
        (unknown h∷ lhs v∷ rhs v∷ env v∷ “refl” v∷ [])

  ℕ-solver : Variable-solver ℕ
  ℕ-solver .Variable-solver.dont-reduce = [ quote _+_ , quote _·_ , quote from-ℕ ]
  ℕ-solver .Variable-solver.build-expr = build-expr
  ℕ-solver .Variable-solver.strat = no
  ℕ-solver .Variable-solver.invoke-solver = “solve”
  ℕ-solver .Variable-solver.invoke-normaliser = “expand”

macro
  repr-nat! : Term → TC ⊤
  repr-nat! = mk-var-repr ℕ-solver

  simpl-nat! : Term → Term → TC ⊤
  simpl-nat! = mk-var-normalise ℕ-solver

  nat! : Term → TC ⊤
  nat! = mk-var-solver ℕ-solver

private
  wow-good-job : ∀ y x z
               → (x + 5 + suc y) · z ＝ z · 5 + x · z + z + z · y
  wow-good-job y x z = nat!
