{-# OPTIONS --safe #-}
module EffTest where

open import Prelude
  hiding (Alt; fail; _<|>_; guard; guardM)
open import Meta.Reflection.Base
  hiding (Alt-TC)

open import Data.Bool as Bool
open import Data.Empty as ⊥
open import Data.Fin.Inductive as Fin
open import Data.List as List
  hiding (Alt-List)
open import Data.Maybe as Maybe
  hiding (Alt-Maybe)

open _-Alg[_]

unquoteDecl sig-iso = declare-record-iso sig-iso (quote Signature)

_
  : {s p : Level}
  → Signature s p
  ≃ Σ[ op ꞉ 𝒰 s ] Π[ ar ꞉ op ] 𝒰 p
_ = ≅→≃ sig-iso

-- Identity effect
𝕀𝕕 : Signature 0ℓ 0ℓ
𝕀𝕕 = ⊥ ▶ λ ()

run-id
  : ∀ {ℓᵃ} {A : Type ℓᵃ}
  → Syntax 𝕀𝕕 A → A
run-id x = ⟦ x ⟧ (mk-alg λ()) id


-- Nondeterminism effect
data NDOp : Type where
  `fail `<|> : NDOp

NDArity : NDOp → Type
NDArity `fail = 0
NDArity `<|>  = 2

ℕ𝔻 : Signature _ _
ℕ𝔻 = NDOp ▶ NDArity

Alt : (M : Effect) → Typeω
Alt = EAlg ℕ𝔻

fail
  : ∀{ℓ} {A : Type ℓ}
  → Syntax ℕ𝔻 A
fail = impure (`fail , λ())

fail!
  : ∀{ℓ} {A : Type ℓ}
    {Δ₀ Δ Δ′ : Signature _ _}
  → ⦃ kek : ℕ𝔻 ∼ Δ₀ ▸ Δ′ ⦄
  → Syntax (Δ₀ ⊕ Δ′) A
fail! ⦃ kek ⦄ = {!!}

qwe : {Δ : Signature _ _} → (Δ ⊕ ℕ𝔻) ∼ Δ ▸ ℕ𝔻
qwe = auto

infixl 3 _<|>_
_<|>_
  : ∀{ℓ} {A : Type ℓ}
  → Syntax ℕ𝔻 A → Syntax ℕ𝔻 A → Syntax ℕ𝔻 A
x <|> y = impure (`<|> , [ x , y ] ∘ lower)

module _ {M : Effect} (let module M = Effect M) ⦃ alt : Alt M ⦄ where

  run-alt
    : ∀ {ℓᵃ} {A : Type ℓᵃ}
      ⦃ appl : Idiom M ⦄
    → Syntax ℕ𝔻 A → M.₀ A
  run-alt x = ⟦ x ⟧ auto pure

  guard
    : ⦃ appl : Idiom M ⦄
    → Bool → M.₀ ⊤
  guard true  = pure tt
  guard false = run-alt fail

  guardM : ⦃ mon : Bind M ⦄
         → M.₀ Bool → M.₀ ⊤
  guardM M = M >>= guard


-- Abstract program

up-to : ℕ → Syntax ℕ𝔻 ℕ
up-to 0       = fail
up-to (suc n) = up-to n <|> pure n

odd? : ℕ → Bool
odd? 0 = false
odd? 1 = true
odd? (suc (suc n)) = odd? n

no-op : ∀{ℓ} {A : Type ℓ} → A → Syntax 𝕀𝕕 A
no-op = pure

odds : ℕ → Syntax ℕ𝔻 ℕ
odds n = do
  m ← up-to n
  guard (odd? m)
  pure m


-- Interpretations

instance
  Alt-List : Alt (eff List)
  Alt-List .unalg (`fail , _) = []
  Alt-List .unalg (`<|>  , k) = k 0 ++ k 1

  Alt-Maybe : Alt (eff Maybe)
  Alt-Maybe .unalg (`fail , _) = nothing
  Alt-Maybe .unalg (`<|>  , k) = case k 0 of λ where
    (just x) → just x
    nothing  → k 1

  Alt-TC : Alt (eff TC)
  Alt-TC .unalg (`fail , k) = type-error []
  Alt-TC .unalg (`<|>  , k) = catchTC (k 0) (k 1)


-- Examples

ex₁ : List ℕ
ex₁ = run-alt (odds 10)

_ : ex₁ ＝ [ 1 , 3 , 5 , 7 , 9 ]
_ = refl

ex₂ : Maybe ℕ
ex₂ = run-alt (odds 10)

_ : ex₂ ＝ just 1
_ = refl

ex₃ : List ℕ
ex₃ = run-alt ⦇ odds 8 + odds 4 ⦈

_ : ex₃ ＝ [ (1 + 1) , (1 + 3) , (3 + 1) , (3 + 3) , (5 + 1) , (5 + 3) , (7 + 1) , (7 + 3) ]
_ = refl

ex₄ : TC ℕ
ex₄ = run-alt (odds 4)

_ : ex₄ ＝ catchTC (catchTC (catchTC (catchTC (type-error []) (type-error [])) (returnTC 1)) (type-error [])) (pure 3)
_ = refl

ex₅ : ℕ
ex₅ = run-id (no-op 1)

_ : ex₅ ＝ 1
_ = refl
