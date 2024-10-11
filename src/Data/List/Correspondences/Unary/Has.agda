{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Has where

open import Prelude

open import Data.List.Base
open import Data.List.Instances.Map
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.Empty.Base

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  P Q R : Pred A ℓ
  x : A
  @0 xs ys : List A

Has : A → @0 List A → Type (level-of-type A)
Has x = Any (_＝ x)

¬Has-[] : ¬ Has x []
¬Has-[] = ¬Any-[]

Any→ΣHas : Any P xs → Σ[ x ꞉ A ] Has x xs × P x
Any→ΣHas (here {x} px) = x , here refl , px
Any→ΣHas (there a)     =
  let (x , h , p) = Any→ΣHas a in
  x , there h , p

All→∀Has : All P xs → (x : A) → Has x xs → P x
All→∀Has     {xs = xs} []            z  hz        = absurd (¬Has-[] hz)
All→∀Has {P} {xs = x ∷ xs} (px ∷ ax) z (here e)   = subst P e px
All→∀Has     {xs = x ∷ xs} (px ∷ ax) z (there hz) = All→∀Has ax z hz

all-has-map : (∀ {x} → Has x xs → P x → Q x)
            → All P xs → All Q xs
all-has-map f []       = []
all-has-map f (p ∷ ps) = f (here refl) p ∷ all-has-map (f ∘ there) ps

has-on-map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {x : A} {@0 xs : List A}
           → (f : A → B) → Has x xs → Has (f x) (map f xs)
has-on-map f (here px) = here (ap f px)
has-on-map f (there a) = there (has-on-map f a)

Has-split : {A : 𝒰 ℓᵃ} {xs : List A} {q : A}
          → Has q xs → Σ[ ls ꞉ List A ] Σ[ rs ꞉ List A ] (xs ＝ ls ++ q ∷ rs)
Has-split {xs = x ∷ xs} (here ex) = [] , xs , ap (_∷ xs) ex
Has-split {xs = x ∷ xs} (there h) =
  let (ls , rs , e) = Has-split h in
  x ∷ ls , rs , ap (x ∷_) e
