{-# OPTIONS --safe #-}
module Data.Tree.Binary.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.IdentitySystem

open import Data.Empty.Base
open import Data.Empty.Instances.HLevel
open import Data.Nat.Base
open import Data.Unit.Instances.HLevel

open import Data.Tree.Binary.Base public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  x y : A
  tl tr xl xr yl yr xs ys : Tree A
  n : HLevel

empty≠leaf : empty ≠ leaf x
empty≠leaf p = subst discrim p tt where
  discrim : Tree A → 𝒰
  discrim empty = ⊤
  discrim _ = ⊥

empty≠node : empty ≠ node tl tr
empty≠node p = subst discrim p tt where
  discrim : Tree A → 𝒰
  discrim empty = ⊤
  discrim _ = ⊥

leaf≠node : leaf x ≠ node tl tr
leaf≠node p = subst discrim p tt where
  discrim : Tree A → 𝒰
  discrim (leaf _) = ⊤
  discrim _ = ⊥

leaf-inj : leaf x ＝ leaf y → x ＝ y
leaf-inj {x} = ap go where
  go : Tree _ → _
  go (leaf x) = x
  go _ = x

node-inj : node xl xr ＝ node yl yr → (xl ＝ yl) × (xr ＝ yr)
node-inj {xl} p = ap go₁ p , ap go₂ p where
  go₁ : Tree _ → _
  go₁ (node tl _) = tl
  go₁ _ = xl
  go₂ : Tree _ → _
  go₂ (node _ tr) = tr
  go₂ _ = xl

module tree-path-code {A : Type ℓ} where

  Code : Tree A → Tree A → Type ℓ
  Code empty empty = Lift _ ⊤
  Code (leaf x) (leaf y) = x ＝ y
  Code (node xl xr) (node yl yr) = Code xl yl × Code xr yr
  Code _ _ = Lift _ ⊥

  code-refl : (t : Tree A) → Code t t
  code-refl empty = lift tt
  code-refl (leaf _) = refl
  code-refl (node tl tr) = code-refl tl , code-refl tr

  decode : Code xs ys → xs ＝ ys
  decode {xs = empty} {ys = empty} _ = refl
  decode {xs = leaf x} {ys = leaf y} = ap leaf
  decode {xs = node xl xr} {ys = node yl yr} (p , q) = ap₂ node (decode p) (decode q)

  code-refl-pathP : (c : Code xs ys) → ＜ code-refl xs ／ (λ i → Code xs (decode c i)) ＼ c ＞
  code-refl-pathP {xs = empty} {ys = empty} _ = refl
  code-refl-pathP {xs = leaf x} {leaf y} p i j = p (i ∧ j)
  code-refl-pathP {xs = node xl xr} {ys = node yl yr} (cl , cr) i = code-refl-pathP cl i , code-refl-pathP cr i

  tree-identity-system : is-identity-system Code code-refl
  tree-identity-system .to-path      = decode
  tree-identity-system .to-path-over = code-refl-pathP

  code-is-of-hlevel : is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code xs ys)
  code-is-of-hlevel {xs = empty} {ys = empty} = hlevel!
  code-is-of-hlevel {xs = empty} {leaf _} = hlevel!
  code-is-of-hlevel {xs = empty} {node _ _} = hlevel!
  code-is-of-hlevel {xs = leaf _} {ys = empty} = hlevel!
  code-is-of-hlevel {xs = leaf x} {leaf y} hl = path-is-of-hlevel′ _ hl x y
  code-is-of-hlevel {xs = leaf _} {node _ _} = hlevel!
  code-is-of-hlevel {xs = node _ _} {ys = empty} = hlevel!
  code-is-of-hlevel {xs = node _ _} {leaf _} = hlevel!
  code-is-of-hlevel {xs = node xl xr} {node yl yr} hl =
    ×-is-of-hlevel _ (code-is-of-hlevel hl) (code-is-of-hlevel hl)

open tree-path-code

tree-is-of-hlevel : (n : HLevel)
                  → is-of-hlevel (2 + n) A
                  → is-of-hlevel (2 + n) (Tree A)
tree-is-of-hlevel n A-hl = is-of-hlevel-η n λ _ _ →
  is-of-hlevel-≃ (suc n)
                 (identity-system-gives-path tree-identity-system ₑ⁻¹)
                 (code-is-of-hlevel A-hl)
