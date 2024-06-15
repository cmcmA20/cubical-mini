{-# OPTIONS --safe --no-exact-split #-}
module Data.Tree.Binary.Path where

open import Meta.Prelude

open import Meta.Extensionality

open import Data.Empty.Base
open import Data.Nat.Base
open import Data.Unit.Base

open import Data.Tree.Binary.Base

private variable
  ℓ ℓ′ ℓᵃ : Level
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


module _ {A : 𝒰 ℓᵃ} ⦃ sa : Extensional A ℓ ⦄ where
  Code-Tree : Tree A → Tree A → Type ℓ
  Code-Tree empty empty = Lift _ ⊤
  Code-Tree (leaf x) (leaf y) = sa .Pathᵉ x y
  Code-Tree (node xl xr) (node yl yr) = Code-Tree xl yl × Code-Tree xr yr
  Code-Tree _ _ = Lift _ ⊥

  code-tree-refl : (t : Tree A) → Code-Tree t t
  code-tree-refl empty = lift tt
  code-tree-refl (leaf x) = sa .reflᵉ x
  code-tree-refl (node tl tr) = code-tree-refl tl , code-tree-refl tr

  decode-tree : Code-Tree xs ys → xs ＝ ys
  decode-tree {xs = empty} {ys = empty} _ = refl
  decode-tree {xs = leaf x} {ys = leaf y} = ap leaf ∘ sa .idsᵉ .to-path
  decode-tree {xs = node xl xr} {ys = node yl yr} (p , q) = ap² node (decode-tree p) (decode-tree q)

  code-tree-reflᴾ : (c : Code-Tree xs ys) → code-tree-refl xs ＝[ ap (Code-Tree xs) (decode-tree c) ]＝ c
  code-tree-reflᴾ {(empty)}    {(empty)} _ = refl
  code-tree-reflᴾ {leaf x}     {leaf y}    = sa .idsᵉ .to-path-over
  code-tree-reflᴾ {node xl xr} {node yl yr} (cl , cr) = code-tree-reflᴾ {xl} cl ,ₚ code-tree-reflᴾ {xr} cr

  instance
    Extensional-Tree : Extensional (Tree A) ℓ
    Extensional-Tree .Pathᵉ = Code-Tree
    Extensional-Tree .reflᵉ = code-tree-refl
    Extensional-Tree .idsᵉ .to-path = decode-tree
    Extensional-Tree .idsᵉ .to-path-over {a} = code-tree-reflᴾ {a}

opaque
  code-is-of-hlevel : is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code-Tree {A = A} xs ys)
  code-is-of-hlevel {n} {xs = empty} {ys = empty} _ = hlevel _
  code-is-of-hlevel {xs = empty} {leaf _} _ = hlevel _
  code-is-of-hlevel {xs = empty} {node _ _} _ = hlevel _
  code-is-of-hlevel {xs = leaf _} {ys = empty} _ = hlevel _
  code-is-of-hlevel {xs = leaf x} {leaf y} hl = path-is-of-hlevel _ hl x y
  code-is-of-hlevel {xs = leaf _} {node _ _} _ = hlevel _
  code-is-of-hlevel {xs = node _ _} {ys = empty} _ = hlevel _
  code-is-of-hlevel {xs = node _ _} {leaf _} _ = hlevel _
  code-is-of-hlevel {xs = node xl xr} {node yl yr} hl =
    ×-is-of-hlevel _ (code-is-of-hlevel {xs = xl} hl) (code-is-of-hlevel {xs = xr} hl)

  tree-is-of-hlevel : (n : HLevel)
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) (Tree A)
  tree-is-of-hlevel n A-hl xs ys =
    ≃→is-of-hlevel (suc n)
                   (identity-system-gives-path (Extensional-Tree .idsᵉ) ⁻¹)
                   (code-is-of-hlevel {xs = xs} A-hl)

instance opaque
  H-Level-binary-tree : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level n A ⦄ → H-Level n (Tree A)
  H-Level-binary-tree {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = tree-is-of-hlevel _ (hlevel n)
  {-# OVERLAPPING H-Level-binary-tree #-}
