{-# OPTIONS --safe #-}
module Meta.Marker where

open import Foundations.Base

open import Meta.Reflection

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Instances.Bind
open import Data.Nat.Base
open import Data.Nat.Instances.Number
open import Data.String.Instances.IsString

private variable
  ℓ : Level
  A : Type ℓ

⌜_⌝ : A → A
⌜ x ⌝ = x
{-# NOINLINE ⌜_⌝ #-}

abstract-marker : Term → Maybe Term
abstract-marker = go 0 where
  go  : ℕ → Term → Maybe Term
  go* : ℕ → List (Arg Term) → Maybe (List (Arg Term))

  go k (var j args) = var j' <$> go* k args
    where
      j' : ℕ
      j' with j <-internal k
      ... | false = suc j
      ... | true = j
  go k (con c args) = con c <$> go* k args
  go k (def f args) with f
  ... | quote ⌜_⌝ = pure (var k [])
  ... | x = def f <$> go* k args
  go k (lam v (abs x t)) = lam v ∘ abs x <$> go (suc k) t
  go k (pat-lam cs args) = nothing
  go k (pi (arg i a) (abs x t)) = do
    t ← go (suc k) t
    a ← go k a
    pure (pi (arg i a) (abs x t))
  go k (agda-sort s) with s
  ... | set t = agda-sort ∘ set <$> go k t
  ... | lit n = pure (agda-sort (lit n))
  ... | prop t = agda-sort ∘ prop <$> go k t
  ... | propLit n = pure (agda-sort (propLit n))
  ... | inf n = pure (agda-sort (inf n))
  ... | unknown = pure (agda-sort unknown)
  go k (lit l) = pure (lit l)
  go k (meta m args) = meta m <$> go* k args
  go k unknown = pure unknown

  go* k [] = pure []
  go* k (arg i x ∷ xs) = do
    x ← go k x
    xs ← go* k xs
    pure (arg i x ∷ xs)

macro
  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the LEFT ENDPOINT of the path. Use
  -- with _≡⟨_⟩_.
  ap! : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ＝ y → Term → TC ⊤
  ap! path goal = do
    goalt ← inferType goal
    just (l , r) ← get-boundary goalt
      where nothing → typeError (strErr "ap!: Goal type " ∷
                                 termErr goalt ∷
                                 strErr " is not a path type" ∷ [])
    just l′ ← pure (abstract-marker l)
      where _ → typeError $ "Failed to abstract over marker in term " ∷ termErr l ∷ []
    let dm = lam visible (abs "x" l′)
    path′ ← quoteTC path
    debugPrint "1lab.marked-ap" 10 $ strErr "original term " ∷ termErr l ∷ []
    debugPrint "1lab.marked-ap" 10 $ strErr "abstracted term " ∷ termErr dm ∷ []
    unify goal (def (quote ap) (dm v∷ path′ v∷ []))

  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the RIGHT ENDPOINT of the path. Use
  -- with _≡˘⟨_⟩_.
  ap¡ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ＝ y → Term → TC ⊤
  ap¡ path goal = do
    goalt ← inferType goal
    just (l , r) ← get-boundary goalt
      where nothing → typeError (strErr "ap¡: Goal type " ∷
                                 termErr goalt ∷
                                 strErr " is not a path type" ∷ [])
    just r′ ← pure (abstract-marker r)
      where _ → typeError $ "Failed to abstract over marker in term " ∷ termErr r ∷ []
    path′ ← quoteTC path
    unify goal $
      def (quote ap) (lam visible (abs "x" r′) v∷ path′ v∷ [])


-- Usage
module _ {ℓ} {A : Type ℓ} {x y : A} {p : x ＝ y} {f : A → (A → A) → A} where
  private
    q : f x (λ y → x) ＝ f y (λ z → y)
    q =
      f ⌜ x ⌝ (λ _ → ⌜ x ⌝) ＝⟨ ap! p ⟩
      f y (λ _ → y)         ∎

    r : f y (λ _ → y) ＝ f x (λ _ → x)
    r =
      f ⌜ y ⌝ (λ _ → ⌜ y ⌝) ＝˘⟨ ap¡ p ⟩
      f x (λ _ → x)         ∎
