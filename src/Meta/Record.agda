{-# OPTIONS --safe #-}
module Meta.Record where

open import Foundations.Base
  renaming ( refl to reflₚ
           ; sym  to symₚ
           ; _∙_  to _∙ₚ_
           )
  renaming ( _∘ˢ_ to _∘ₜˢ_
           ; _∘_  to _∘ₜ_
           )
open import Foundations.Isomorphism public

open import Meta.Effect.Foldable
open import Meta.Groupoid
open import Meta.Literals.FromNat
open import Meta.Literals.FromProduct
open import Meta.Literals.FromString
open import Meta.Reflection.Base

open import Data.Bool.Base
open import Data.List.Base as List
open import Data.List.Instances.Append
open import Data.List.Instances.Foldable
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Map
open import Data.Reflection.Abs
open import Data.Reflection.Argument
open import Data.Reflection.Error
open import Data.Reflection.Fixity
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Term

private variable
  ℓ : Level
  A : Type ℓ

field-names→sigma : List A → Term
field-names→sigma [] = def (quote ⊤) []
field-names→sigma (_ ∷ []) = unknown
field-names→sigma (_ ∷ xs) =
  def (quote Σ) (lam visible (abs "_" (field-names→sigma xs)) v∷ [])

Fields : Type
Fields = List (Name × List Name)

field-names→paths : List (Arg Name) → Fields
field-names→paths [] = []
field-names→paths (arg _ nm ∷ []) = (nm , []) ∷ []
field-names→paths (arg _ x ∷ (y ∷ ys)) with field-names→paths (y ∷ ys)
... | fields = (x , [ quote fst ]) ∷ map (second (quote snd ∷_)) fields

record→iso : Name → (List (Arg Term) → TC Term) → TC Term
record→iso namen unfolded =
  (infer-type (def namen []) >>= normalise) >>= go []
  where
  go : List Arg-info → Term → TC Term
  go acc (pi argu@(arg i@(arg-info _ m) argTy) (abs s ty)) = do
    r ← extend-context "arg" argu $ go (i ∷ acc) ty
    pure $ pi (arg (arg-info hidden m) argTy) (abs s r)
  go acc (agda-sort _) = do
    let rec = def namen (makeArgs 0 [] acc)
    unfolded ← unfolded (implicitArgs 0 [] acc)
    pure $ def (quote Iso) (rec v∷ unfolded v∷ [])
    where
      makeArgs : ℕ → List (Arg Term) → List Arg-info → List (Arg Term)
      makeArgs n acc [] = acc
      makeArgs n acc (i ∷ infos) = makeArgs (suc n) (arg i (var n []) ∷ acc) infos

      implicitArgs : ℕ → List (Arg Term) → List Arg-info → List (Arg Term)
      implicitArgs n acc [] = acc
      implicitArgs n acc (_ ∷ i) = implicitArgs (suc n) (var n [] h∷ acc) i
  go _ _ = type-error [ "Not a record type name: " , name-err namen ]

undo-clause : Name × List Name → Clause
undo-clause (r-field , sel-path) = clause
  (("sig" , argN unknown) ∷ [])
  [ argN (proj (quote snd))
  , argN (proj (quote is-iso.inv))
  , argN (var 0)
  , argN (proj r-field)
  ]
  (fold-r (λ n t → def n (t v∷ [])) (var 0 []) (reverse sel-path))

redo-clause : Name × List Name → Clause
redo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ [])
  (argN (proj (quote fst)) ∷ argN (var 0) ∷ map (argN ∘ˢ proj) sel-path)
  (def r-field (var 0 [] v∷ []))

undo-redo-clause : Name × List Name → Clause
undo-redo-clause ((r-field , _)) = clause
  (("sig" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  ( argN (proj (quote snd)) ∷ argN (proj (quote is-iso.linv))
  ∷ argN (var 1) ∷ argN (var 0) ∷ argN (proj r-field) ∷ [])
  (def r-field (var 1 [] v∷ []))

redo-undo-clause : Name × List Name → Clause
redo-undo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  (  [ argN (proj (quote snd)) , argN (proj (quote is-iso.rinv)) , argN (var 1) , argN (var 0) ]
  <> map (argN ∘ˢ proj) sel-path)
  (fold-r (λ n t → def n (t v∷ [])) (var 1 []) (reverse sel-path))

pi-term→sigma : Term → TC Term
pi-term→sigma (pi (arg _ x) (abs n (def n′ _))) = pure x
pi-term→sigma (pi (arg _ x) (abs n y)) = do
  sig ← pi-term→sigma y
  pure $ def (quote Σ) (x v∷ lam visible (abs n sig) v∷ [])
pi-term→sigma _ = type-error "Not a record type constructor! "

instantiate′ : Term → Term → Term
instantiate′ (pi _ (abs _ xs)) (pi _ (abs _ b)) = instantiate′ xs b
instantiate′ (agda-sort _) tm = tm
instantiate′ _ tm = tm

make-record-iso-sigma : Bool → TC Name → Name → TC Name
make-record-iso-sigma declare? getName `R = do
  record-type `R-con fields ← get-definition `R
    where _ → type-error [ name-err `R , " is not a record type" ]

  let fields = field-names→paths fields

  `R-ty ← get-type `R
  con-ty ← get-type `R-con
  ty ← record→iso `R λ args → do
    let con-ty = instantiate′ `R-ty con-ty
    `S ← pi-term→sigma con-ty
    pure `S

  nm ← getName
  pure declare? >>= λ where
    true  → declare-def (argN nm) ty
    false → pure tt

  define-function nm
    ( map redo-clause fields <>
      map undo-clause fields <>
      map redo-undo-clause fields <>
      map undo-redo-clause fields)
  pure nm


declare-record-iso : Name → Name → TC ⊤
declare-record-iso nm rec = do
  make-record-iso-sigma true (pure nm) rec
  pure tt

define-record-iso : Name → Name → TC ⊤
define-record-iso nm rec = do
  make-record-iso-sigma false (pure nm) rec
  pure tt


-- Usage
private
  module _ {ℓ} (A : Type ℓ) where
    record T : Type ℓ where
      no-eta-equality
      field
        ⦃ fp ⦄ : A
        {f} : A → A
        fixed : f fp ＝ fp

    unquoteDecl eqv = declare-record-iso eqv (quote T)

    _ : Iso T (Σ A (λ fp → Σ (A → A) (λ f → f fp ＝ fp)))
    _ = eqv

  unquoteDecl eqv-outside = declare-record-iso eqv-outside (quote T)

  _ : {ℓ : Level} {A : Type ℓ} → Iso (T A) (Σ A (λ fp → Σ (A → A) (λ f → f fp ＝ fp)))
  _ = eqv-outside

  module _ (x : ℕ) where
    unquoteDecl eqv-extra = declare-record-iso eqv-extra (quote T)

  _ : ℕ → {ℓ : Level} {A : Type ℓ}
    → Iso (T A) (Σ A (λ fp → Σ (A → A) (λ f → f fp ＝ fp)))
  _ = eqv-extra

  record T2 : Type where
    -- works without eta equality too
    field
      some-field : ℕ

  s-eqv : Iso T2 ℕ
  unquoteDef s-eqv = define-record-iso s-eqv (quote T2)

  Bar : Type
  Bar = ℕ

  private variable Z : Bar

  Baz : Bar → Type
  Baz 0 = Bool
  Baz _ = ℕ

  record Foo : Type where
    field
      foo : Baz Z

  -- works only with a full signature
  -- see agda/cubical issue #995
  foo-iso : Iso Foo ({A : Bar} → Baz A)
  unquoteDef foo-iso = define-record-iso foo-iso (quote Foo)


  -- also works with erased record arguments
  -- (but not erased fields, so you have to wrap them)
  record Zooz (@0 n : ℕ) : Type where
    field
      foo : ℕ
      bar : Erased ℕ

  unquoteDecl zooz-iso = declare-record-iso zooz-iso (quote Zooz)
