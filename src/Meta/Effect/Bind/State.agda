{-# OPTIONS --safe #-}
module Meta.Effect.Bind.State where

open import Foundations.Base
open import Data.Unit

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Effect.Idiom
open import Meta.Effect.Bind
open import Meta.Effect.Choice
open import Meta.Effect.Alt

private
  variable
    ℓa ℓs ℓ : Level
    A : 𝒰 ℓa
    S : 𝒰 ℓs

-- State monad operations

record BindState (S : 𝒰 ℓs) (M : Effect) : Typeω where
  private module M = Effect M
  field
    gets   : (S → A) → M.₀ A
    modify : (S → S) → M.₀ ⊤
    ⦃ Bind-state ⦄ : Bind M

  put : S → M.₀ ⊤
  put = modify ∘ (λ _ → id)

  get : M.₀ S
  get = gets id

open BindState ⦃ ... ⦄

-- State monad transformer

record StateT
       (S : 𝒰 ℓs)
       (M : Effect)
       (A : 𝒰 ℓa)
       : 𝒰 (ℓs ⊔ Effect.adj M (ℓs ⊔ ℓa)) where
  constructor mkstatet
  private module M = Effect M
  field run-stateT : S → M.₀ (S × A)
open StateT public

module _ {M : Effect} (let module M = Effect M) ⦃ mp : Map M ⦄ where

  open Map ⦃ ... ⦄

  instance
    map-stateT : Map (eff (StateT S M))
    map-stateT .Map.map f (mkstatet r) = mkstatet (map (second f) ∘ r)

  eval-stateT : StateT S M A → S → M.₀ A
  eval-stateT ma s = snd <$> run-stateT ma s

  exec-stateT : StateT S M A → S → M.₀ S
  exec-stateT ma s = fst <$> run-stateT ma s

module _ {M : Effect} (let module M = Effect M) ⦃ bd : Bind M ⦄ where

  open Idiom ⦃ ... ⦄
  open Bind ⦃ ... ⦄

  instance
    idiom-stateT : Idiom (eff (StateT S M))
    idiom-stateT .Idiom.Map-idiom = map-stateT {M = M}
    idiom-stateT .Idiom.pure x .run-stateT s = pure (s , x)
    idiom-stateT .Idiom._<*>_ mf mx .run-stateT s =
      do (s′ , f) ← run-stateT mf s
         (s″ , x) ← run-stateT mx s′
         pure (s″ , f x)

    bind-stateT : Bind (eff (StateT S M))
    bind-stateT .Bind.Idiom-bind = idiom-stateT
    bind-stateT .Bind._>>=_ ma f .run-stateT s =
      do (s′ , a) ← run-stateT ma s
         run-stateT (f a) s′

    bindstate-stateT : BindState S (eff (StateT S M))
    bindstate-stateT .BindState.Bind-state = bind-stateT
    bindstate-stateT .BindState.gets f .run-stateT s = pure (s , f s)
    bindstate-stateT .BindState.modify f .run-stateT s = pure (f s , tt)

module _ {M : Effect} (let module M = Effect M) ⦃ ch : Choice M ⦄ where

  open Choice ⦃ ... ⦄

  instance
    choice-stateT : Choice (eff (StateT S M))
    choice-stateT .Choice._<|>_ ma mb .run-stateT s =
      run-stateT ma s <|> run-stateT mb s

module _ {M : Effect} (let module M = Effect M) ⦃ ch : Alt M ⦄ where

  open Alt ⦃ ... ⦄

  instance
    alt-stateT : Alt (eff (StateT S M))
    alt-stateT .Alt.Choice-alt = choice-stateT {M = M}
    alt-stateT .Alt.fail .run-stateT _ = fail

-- State

State : 𝒰 ℓs → 𝒰 ℓa → 𝒰 (ℓs ⊔ ℓa)
State S = StateT S (eff id)

-- TODO lawful
