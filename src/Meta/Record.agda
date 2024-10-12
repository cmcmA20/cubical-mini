{-# OPTIONS --safe --no-exact-split #-}
module Meta.Record where

open import Meta.Prelude

open import Meta.Effect.Foldable
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
open import Data.Unit.Base

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
    pure $ def (quote Isoₜ) (rec v∷ unfolded v∷ [])
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
  [ argN (proj (quote Iso.from))
  , argN (var 0)
  , argN (proj r-field)
  ]
  (fold-r (λ n t → def n (t v∷ [])) (var 0 []) (reverse sel-path))

redo-clause : Name × List Name → Clause
redo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ [])
  (argN (proj (quote Iso.to)) ∷ argN (var 0) ∷ map (proj ∙ argN) sel-path)
  (def r-field (var 0 [] v∷ []))

undo-redo-clause : Name × List Name → Clause
undo-redo-clause ((r-field , _)) = clause
  (("sig" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  ( argN (proj (quote Iso.inverses)) ∷ argN (proj (quote Inverses.inv-i))
  ∷ argN (var 0) ∷ argN (var 1) ∷ argN (proj r-field) ∷ [])
  (def r-field (var 1 [] v∷ []))

redo-undo-clause : Name × List Name → Clause
redo-undo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  (  [ argN (proj (quote Iso.inverses)) , argN (proj (quote Inverses.inv-o)) , argN (var 0) , argN (var 1) ]
  <> map (proj ∙ argN) sel-path)
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


-- TODO move this

has-section-Iso
  : {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
    {I : B → A → 𝒰 ℓ′} {O : A → B → 𝒰 ℓ} {I∙O : B → B → 𝒰 ℓ″}
    ⦃ _ : Refl I∙O ⦄ ⦃ _ : Comp I O I∙O ⦄ {x : A} {y : B} {r : O x y}
  → has-section r ≅ Σ[ s ꞉ I y x ] s section-of r
unquoteDef has-section-Iso = define-record-iso has-section-Iso (quote has-section)

has-retraction-Iso
  : {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
    {I : A → B → 𝒰 ℓ′} {O : B → A → 𝒰 ℓ} {I∙O : A → A → 𝒰 ℓ″}
    ⦃ _ : Refl I∙O ⦄ ⦃ _ : Comp I O I∙O ⦄ {x : A} {y : B} {s : I x y}
  → has-retraction s ≅ Σ[ r ꞉ O y x ] r retraction-of s
unquoteDef has-retraction-Iso = define-record-iso has-retraction-Iso (quote has-retraction)

Inverses-Iso
  : {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
    {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
    {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
    ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
    ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
    {x : A} {y : B} {f : F x y} {g : G y x}
  → Inverses f g ≅ (f retraction-of g) × (f section-of g)
unquoteDef Inverses-Iso = define-record-iso Inverses-Iso (quote Inverses)

quasi-inverse-Iso
  : {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
    {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
    {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
    ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
    ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
    {x : A} {y : B} {f : F x y}
  → quasi-inverse f ≅ Σ[ g ꞉ G y x ] Inverses f g
unquoteDef quasi-inverse-Iso = define-record-iso quasi-inverse-Iso (quote quasi-inverse)

Iso-Iso
  : {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
    {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
    {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
    ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
    ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
    {x : A} {y : B}
  → Iso F G x y ≅ Σ[ f ꞉ F x y ] Σ[ g ꞉ G y x ] Inverses f g
unquoteDef Iso-Iso = define-record-iso Iso-Iso (quote Iso)


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

    _ : T ≅ Σ A (λ fp → Σ (A → A) (λ f → f fp ＝ fp))
    _ = eqv

  unquoteDecl eqv-outside = declare-record-iso eqv-outside (quote T)

  _ : {ℓ : Level} {A : Type ℓ} → T A ≅ Σ A (λ fp → Σ (A → A) (λ f → f fp ＝ fp))
  _ = eqv-outside

  module _ (x : ℕ) where
    unquoteDecl eqv-extra = declare-record-iso eqv-extra (quote T)

  _ : ℕ → {ℓ : Level} {A : Type ℓ}
    → T A ≅ Σ A (λ fp → Σ (A → A) (λ f → f fp ＝ fp))
  _ = eqv-extra

  record T2 : Type where
    -- works without eta equality too
    field
      some-field : ℕ

  s-eqv : T2 ≅ ℕ
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
  foo-iso : Foo ≅ ({A : Bar} → Baz A)
  unquoteDef foo-iso = define-record-iso foo-iso (quote Foo)


  -- also works with erased record arguments
  -- (but not erased fields, so you have to wrap them)
  record Zooz (@0 n : ℕ) : Type where
    field
      foo : ℕ
      bar : Erased ℕ

  unquoteDecl zooz-iso = declare-record-iso zooz-iso (quote Zooz)
