{-# OPTIONS --safe #-}
module Categories.Solver where

open import Foundations.Base hiding (id; _∘_)

open import Meta.Marker
open import Meta.Reflection.Base
open import Meta.Reflection.Solver

open import Categories.Base

open import Data.List.Base

private variable
  o h : Level

module NbE (Cat : Precategory o h) where
  open Precategory Cat

  private variable
    A B C : Ob

  data Expr : Ob → Ob → Type (o ⊔ h) where
    `id  : Expr A A
    _`∘_ : Expr B C → Expr A B → Expr A C
    _↑   : Hom A B → Expr A B

  infixr 40 _`∘_
  infix 50 _↑

  embed : Expr A B → Hom A B
  embed `id      = id
  embed (f ↑)    = f
  embed (f `∘ g) = embed f ∘ embed g

  eval : Expr B C → Hom A B → Hom A C
  eval `id f      = f
  eval (f ↑) g    = f ∘ g
  eval (f `∘ g) h = eval f (eval g h)

  nf : Expr A B → Hom A B
  nf e = eval e id

  eval-sound-k : (e : Expr B C) (f : Hom A B) → eval e f ＝ embed e ∘ f
  eval-sound-k `id f = sym (id-l _) -- f ＝ id ∘ f
  eval-sound-k (f `∘ g) h =
    eval f (eval g h)       ＝⟨ eval-sound-k f _ ⟩
    embed f ∘ eval g h      ＝⟨ ap (embed f ∘_) (eval-sound-k g _) ⟩
    embed f ∘ embed g ∘ h   ＝⟨ assoc _ _ _ ⟩
    (embed f ∘ embed g) ∘ h ∎
  eval-sound-k (x ↑) f = refl -- x ∘ f ＝ x ∘ f

  eval-sound : (e : Expr A B) → nf e ＝ embed e
  eval-sound e = eval-sound-k e id ∙ id-r _

  opaque
    solve : (f g : Expr A B) → nf f ＝ nf g → embed f ＝ embed g
    solve f g p = sym (eval-sound f) ∙∙ p ∙∙ (eval-sound g)

    solve-filler : (f g : Expr A B) → (p : nf f ＝ nf g) → Square (eval-sound f) p (eval-sound g) (solve f g p)
    solve-filler f g p = ∙∙-filler (sym (eval-sound f)) p (eval-sound g)

module Reflection where

  pattern category-args xs =
    _ hm∷ _ hm∷ _ v∷ xs

  pattern “id” =
    def (quote Precategory.id) (category-args (_ h∷ []))

  pattern “∘” f g =
    def (quote Precategory._∘_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

  mk-category-args : Term → List (Arg Term) → List (Arg Term)
  mk-category-args cat xs = unknown h∷ unknown h∷ cat v∷ xs

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs = def (quote NbE.solve) $ mk-category-args cat $
    infer-hidden′ 2 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ []

  “nf” : Term → Term → Term
  “nf” cat e = def (quote NbE.nf) (mk-category-args cat $ infer-hidden′ 2 $ varg e ∷ [])

  build-expr : Term → Term
  build-expr “id” = con (quote NbE.`id) []
  build-expr (“∘” f g) = con (quote NbE._`∘_) (build-expr f v∷ build-expr g v∷ [])
  build-expr (def (quote ⌜_⌝) (_ h∷ _ h∷ tm v∷ [])) = build-expr tm
  build-expr f = con (quote NbE._↑) (f v∷ [])

  dont-reduce : List Name
  dont-reduce = quote Precategory.id ∷ quote Precategory._∘_ ∷ []

  cat-solver : Term → Simple-solver
  cat-solver cat .Simple-solver.dont-reduce = dont-reduce
  cat-solver cat .Simple-solver.build-expr tm = pure $ build-expr tm
  cat-solver cat .Simple-solver.strat = no
  cat-solver cat .Simple-solver.invoke-solver = “solve” cat
  cat-solver cat .Simple-solver.invoke-normaliser = “nf” cat

  repr-macro : Term → Term → Term → TC ⊤
  repr-macro cat = mk-simple-repr (cat-solver cat)

  simplify-macro : Term → Term → Term → TC ⊤
  simplify-macro cat = mk-simple-normalise (cat-solver cat)

  solve-macro : Term → Term → TC ⊤
  solve-macro cat = mk-simple-solver (cat-solver cat)

macro
  repr-cat! : Term → Term → Term → TC ⊤
  repr-cat! = Reflection.repr-macro

  simpl-cat! : Term → Term → Term → TC ⊤
  simpl-cat! = Reflection.simplify-macro

  cat! : Term → Term → TC ⊤
  cat! = Reflection.solve-macro

module _ (C : Precategory o h) where private
  open module C = Precategory C
  variable
    A B : C.Ob
    a b c d : C.Hom A B

  test :  a ∘ (b ∘ (c ∘ id) ∘ id ∘ (d ∘ id))
       ＝ a ∘  b ∘  c ∘             d
  test = cat! C
