{-# OPTIONS --safe --no-exact-split #-}
module Data.Tree.Binary.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base
open import Data.Nat.Base
open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

open import Data.Tree.Binary.Base as Tree

private variable
  ℓ ℓ′ ℓᵃ : Level
  A : Type ℓ
  x y : A
  tl tr xl xr yl yr xs ys : Tree A
  n : HLevel
  b b₁ b₂ : Bool

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

instance
  Reflects-empty≠leaf : Reflects (Tree.empty ＝ leaf x) false
  Reflects-empty≠leaf = ofⁿ (λ p → ¬-so-false (subst So (ap is-empty? p) oh))

  Reflects-leaf≠empty : Reflects (leaf x ＝ Tree.empty) false
  Reflects-leaf≠empty = ofⁿ (λ p → ¬-so-false (subst So (ap is-leaf? p) oh))

  Reflects-empty≠node : Reflects (Tree.empty ＝ node tl tr) false
  Reflects-empty≠node = ofⁿ (λ p → ¬-so-false (subst So (ap is-empty? p) oh))

  Reflects-node≠empty : Reflects (node tl tr ＝ Tree.empty) false
  Reflects-node≠empty = ofⁿ (λ p → ¬-so-false (subst So (ap is-node? p) oh))

  Reflects-leaf≠node : Reflects (leaf x ＝ node tl tr) false
  Reflects-leaf≠node = ofⁿ (λ p → ¬-so-false (subst So (ap is-leaf? p) oh))

  Reflects-node≠leaf : Reflects (node tl tr ＝ leaf x) false
  Reflects-node≠leaf = ofⁿ (λ p → ¬-so-false (subst So (ap is-node? p) oh))

  Reflects-leaf=leaf : ⦃ Reflects (Path A x y) b ⦄ → Reflects (leaf x ＝ leaf y) b
  Reflects-leaf=leaf = Reflects.dmap (ap leaf) (contra leaf-inj) auto

  Reflects-node=node
    : ⦃ _ : Reflects (xl ＝ yl) b₁ ⦄ ⦃ _ : Reflects (xr ＝ yr) b₂ ⦄
    → Reflects (node xl xr ＝ node yl yr) (b₁ and b₂)
  Reflects-node=node =
    Reflects.dmap (λ p → ap² node (p .fst) (p .snd)) (contra < fst ∘ node-inj , snd ∘ node-inj >) auto

  Tree-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Tree A)
  Tree-is-discrete {x = Tree.empty} {(Tree.empty)} = true because auto
  Tree-is-discrete {x = Tree.empty} {leaf y}       = false because auto
  Tree-is-discrete {x = Tree.empty} {node yl yr}   = false because auto
  Tree-is-discrete {x = leaf x}     {(Tree.empty)} = false because auto
  Tree-is-discrete {x = leaf x}     {leaf y}       = x =? y because auto
  Tree-is-discrete {x = leaf x}     {node yl yr}   = false because auto
  Tree-is-discrete {x = node xl xr} {(Tree.empty)} = false because auto
  Tree-is-discrete {x = node xl xr} {leaf y}       = false because auto
  Tree-is-discrete {x = node xl xr} {node yl yr} .does  =
    ⌊ Tree-is-discrete {x = xl} {y = yl} ⌋ and ⌊ Tree-is-discrete {x = xr} {y = yr} ⌋
  Tree-is-discrete {x = node xl xr} {node yl yr} .proof =
    Reflects-node=node ⦃ Tree-is-discrete .proof ⦄ ⦃ Tree-is-discrete .proof ⦄

opaque
  empty≠leaf : Tree.empty ≠ leaf x
  empty≠leaf = false!

opaque
  empty≠node : Tree.empty ≠ node tl tr
  empty≠node = false!

opaque
  leaf≠node : leaf x ≠ node tl tr
  leaf≠node = false!

module _ {A : 𝒰 ℓᵃ} ⦃ sa : Extensional A ℓ ⦄ where
  Code-Tree : Tree A → Tree A → Type ℓ
  Code-Tree empty empty = ⊤
  Code-Tree (leaf x) (leaf y) = sa .Pathᵉ x y
  Code-Tree (node xl xr) (node yl yr) = Code-Tree xl yl × Code-Tree xr yr
  Code-Tree _ _ = ⊥

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
