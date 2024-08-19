{-# OPTIONS --safe --no-exact-split #-}
module Data.Reflection.Instances.Discrete where

open import Foundations.Prelude

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Char.Path
open import Data.Dec.Base as Dec
open import Data.Float.Path
open import Data.Id.Inductive
open import Data.List.Base
open import Data.List.Path
open import Data.Nat.Path
open import Data.String.Path
open import Data.Word.Path

open import Data.Reflection.Abs
open import Data.Reflection.Argument
open import Data.Reflection.Fixity
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Properties
open import Data.Reflection.Term

private variable
  ℓ : Level
  A : Type ℓ

-- Abs

instance
  Abs-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Abs A)
  Abs-is-discrete = ↣→is-discrete!
    $ < abs-name , abs-binder >
    , λ p → abs-ext (ap fst p) (ap snd p)


-- Argument
instance
  Visibility-is-discrete : is-discrete Visibility
  Visibility-is-discrete = is-discreteⁱ→is-discrete λ where
    visible visible   → yes reflⁱ
    visible hidden    → no λ ()
    visible instance′ → no λ ()

    hidden visible      → no λ ()
    hidden hidden       → yes reflⁱ
    hidden instance′    → no λ ()

    instance′ visible   → no λ ()
    instance′ hidden    → no λ ()
    instance′ instance′ → yes reflⁱ

  Relevance-is-discrete : is-discrete Relevance
  Relevance-is-discrete = is-discreteⁱ→is-discrete λ where
    relevant relevant   → yes reflⁱ
    relevant irrelevant → no λ ()

    irrelevant relevant   → no λ ()
    irrelevant irrelevant → yes reflⁱ

  Quantity-is-discrete : is-discrete Quantity
  Quantity-is-discrete = is-discreteⁱ→is-discrete λ where
    quantity-0 quantity-0 → yes reflⁱ
    quantity-0 quantity-ω → no λ ()
    quantity-ω quantity-0 → no λ ()
    quantity-ω quantity-ω → yes reflⁱ

  Modality-is-discrete : is-discrete Modality
  Modality-is-discrete = ↣→is-discrete!
    $ < modality→relevance , modality→quantity >
    , λ p → modality-ext (ap fst p) (ap snd p)

  Arg-info-is-discrete : is-discrete Arg-info
  Arg-info-is-discrete = ↣→is-discrete!
    $ < arg-vis , arg-modality >
    , (λ p → arg-info-ext (ap fst p) (ap snd p))

  Arg-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Arg A)
  Arg-is-discrete = ↣→is-discrete!
    $ < unai , unarg >
    , (λ p → arg-ext (ap fst p) (ap snd p))


-- Fixity

instance
  Associativity-is-discrete : is-discrete Associativity
  Associativity-is-discrete = is-discreteⁱ→is-discrete λ where
    left-assoc  left-assoc  → yes reflⁱ
    left-assoc  right-assoc → no λ ()
    left-assoc  non-assoc   → no λ ()

    right-assoc left-assoc  → no λ ()
    right-assoc right-assoc → yes reflⁱ
    right-assoc non-assoc   → no λ ()

    non-assoc   left-assoc  → no λ ()
    non-assoc   right-assoc → no λ ()
    non-assoc   non-assoc   → yes reflⁱ

  Precedence-is-discrete : is-discrete Precedence
  Precedence-is-discrete = is-discreteⁱ→is-discrete λ where
    (related x) (related y) → caseᵈ x ＝ⁱ y of λ where
      (yes x=y) → yes (apⁱ related x=y)
      (no ¬a) → no λ { reflⁱ → ¬a reflⁱ }
    unrelated unrelated → yes reflⁱ
    (related x) unrelated → no λ ()
    unrelated (related x) → no λ ()

  Fixity-is-discrete : is-discrete Fixity
  Fixity-is-discrete = is-discreteⁱ→is-discrete λ where
    (fixity a p) (fixity a′ p′) → caseᵈ (a ＝ⁱ a′) of λ where
      (yes a=a′) → caseᵈ (p ＝ⁱ p′) of λ where
        (yes p=p′) → yes (apⁱ² fixity a=a′ p=p′)
        (no ¬ps)   → no λ ps → ¬ps (apⁱ fixity→precedence ps)
      (no  ¬as)  → no λ { reflⁱ → ¬as reflⁱ }


-- Meta

instance
  Meta-is-discrete : is-discrete Meta
  Meta-is-discrete = ↣→is-discrete! (meta→ℕ , meta→ℕ-inj)


-- Name

instance
  Name-is-discrete : is-discrete Name
  Name-is-discrete = ↣→is-discrete! (name→words64 , name→words64-inj)


-- Literal

instance
  Literal-is-discrete : is-discrete Literal
  Literal-is-discrete = is-discreteⁱ→is-discrete λ where
    (nat n) (nat n₁) → caseᵈ n ＝ⁱ n₁ of λ where
      (yes n=n₁) → yes (apⁱ nat n=n₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }
    (word64 n) (word64 n₁) → caseᵈ n ＝ⁱ n₁ of λ where
      (yes n=n₁) → yes (apⁱ word64 n=n₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }
    (float x) (float x₁) → caseᵈ x ＝ⁱ x₁ of λ where
      (yes x=x₁) → yes (apⁱ float x=x₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }
    (char c) (char c₁) → caseᵈ c ＝ⁱ c₁ of λ where
      (yes c=c₁) → yes (apⁱ char c=c₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }
    (string s) (string s₁) → caseᵈ s ＝ⁱ s₁ of λ where
      (yes s=s₁) → yes (apⁱ string s=s₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }
    (name x) (name x₁) → caseᵈ x ＝ⁱ x₁ of λ where
      (yes x=x₁) → yes (apⁱ name x=x₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }
    (meta x) (meta x₁) → caseᵈ x ＝ⁱ x₁ of λ where
      (yes x=x₁) → yes (apⁱ meta x=x₁)
      (no ¬p) → no λ { reflⁱ → ¬p reflⁱ }

    (nat n) (word64 n₁) → no λ ()
    (nat n) (float x)   → no λ ()
    (nat n) (char c)    → no λ ()
    (nat n) (string s)  → no λ ()
    (nat n) (name x)    → no λ ()
    (nat n) (meta x)    → no λ ()
    (word64 n) (nat n₁)    → no λ ()
    (word64 n) (float x)   → no λ ()
    (word64 n) (char c)    → no λ ()
    (word64 n) (string s)  → no λ ()
    (word64 n) (name x)    → no λ ()
    (word64 n) (meta x)    → no λ ()
    (float x) (nat n)    → no λ ()
    (float x) (word64 n) → no λ ()
    (float x) (char c)   → no λ ()
    (float x) (string s) → no λ ()
    (float x) (name x₁)  → no λ ()
    (float x) (meta x₁)  → no λ ()
    (char c) (nat n)    → no λ ()
    (char c) (word64 n) → no λ ()
    (char c) (float x)  → no λ ()
    (char c) (string s) → no λ ()
    (char c) (name x)   → no λ ()
    (char c) (meta x)   → no λ ()
    (string s) (nat n)     → no λ ()
    (string s) (word64 n)  → no λ ()
    (string s) (float x)   → no λ ()
    (string s) (char c)    → no λ ()
    (string s) (name x)    → no λ ()
    (string s) (meta x)    → no λ ()
    (name x) (nat n)    → no λ ()
    (name x) (word64 n) → no λ ()
    (name x) (float x₁) → no λ ()
    (name x) (char c)   → no λ ()
    (name x) (string s) → no λ ()
    (name x) (meta x₁)  → no λ ()
    (meta x) (nat n)    → no λ ()
    (meta x) (word64 n) → no λ ()
    (meta x) (float x₁) → no λ ()
    (meta x) (char c)   → no λ ()
    (meta x) (string s) → no λ ()
    (meta x) (name x₁)  → no λ ()


-- Term

private
  term-discrete : (x y : Term) → Dec (x ＝ⁱ y)
  sort-discrete : (x y : Sort) → Dec (x ＝ⁱ y)
  clause-discrete : (x y : Clause) → Dec (x ＝ⁱ y)
  pattern-discrete : (x y : Pattern) → Dec (x ＝ⁱ y)

  abs-term-discrete : (x y : Abs Term) → Dec (x ＝ⁱ y)
  arg-term-discrete : (x y : Arg Term) → Dec (x ＝ⁱ y)
  args-discrete : (xs ys : Args) → Dec (xs ＝ⁱ ys)
  tel-discrete : (xs ys : Telescope) → Dec (xs ＝ⁱ ys)
  clauses-discrete : (xs ys : List Clause) → Dec (xs ＝ⁱ ys)
  arg-pattern-discrete : (x y : Arg Pattern) → Dec (x ＝ⁱ y)
  patterns-discrete : (xs ys : Patterns) → Dec (xs ＝ⁱ ys)

  term-discrete (var x args) (var x₁ args₁) = caseᵈ x ＝ⁱ x₁ of λ where
    (yes x=x₁) → case (args-discrete args args₁) return (λ _ → Dec (var x args ＝ⁱ var x₁ args₁)) of λ where
      (yes a=a₁) → yes (apⁱ² var x=x₁ a=a₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ get-args ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (con c args) (con c₁ args₁) = caseᵈ c ＝ⁱ c₁ of λ where
    (yes c=c₁) → case (args-discrete args args₁) return (λ _ → Dec (_＝ⁱ_ {A = Term} (con c args) (con c₁ args₁))) of λ where
      (yes a=a₁) → yes (apⁱ² con c=c₁ a=a₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ get-args ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (pat-lam cs args) (pat-lam cs₁ args₁) = case clauses-discrete cs cs₁ return (λ _ → Dec (pat-lam cs args ＝ⁱ pat-lam cs₁ args₁)) of λ where
    (yes cs=cs₁) → case (args-discrete args args₁) return (λ d → Dec (pat-lam cs args ＝ⁱ pat-lam cs₁ args₁)) of λ where
      (yes a=a₁) → yes (apⁱ² pat-lam cs=cs₁ a=a₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ get-args ps)
    (no ¬as)     → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (agda-sort s) (agda-sort s₁) = case (sort-discrete s s₁) return (λ _ → Dec (agda-sort s ＝ⁱ agda-sort s₁)) of λ where
    (yes s=s₁) → yes (apⁱ agda-sort s=s₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (lit l) (lit l₁) = caseᵈ (l ＝ⁱ l₁) of λ where
    (yes l=l₁) → yes (apⁱ lit l=l₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (meta x x₁) (meta x₂ x₃) = caseᵈ (x ＝ⁱ x₂) of λ where
    (yes x=x₂) → case (args-discrete x₁ x₃) return (λ _ → Dec (meta x x₁ ＝ⁱ meta x₂ x₃)) of λ where
      (yes x₁=x₃) → yes (apⁱ² meta x=x₂ x₁=x₃)
      (no ¬ps)    → no λ ps → ¬ps (apⁱ get-args ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (lam v t) (lam v₁ t₁) = caseᵈ (v ＝ⁱ v₁) of λ where
    (yes v=v₁) → case (abs-term-discrete t t₁) return (λ _ → Dec (lam v t ＝ⁱ lam v₁ t₁)) of λ where
      (yes t=t₁) → yes (apⁱ² lam v=v₁ t=t₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ get-abs ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (pi a b) (pi a₁ b₁) = case (arg-term-discrete a a₁) return (λ _ → Dec (pi a b ＝ⁱ pi a₁ b₁)) of λ where
    (yes a=a₁) → case (abs-term-discrete b b₁) return (λ _ → Dec (pi a b ＝ⁱ pi a₁ b₁)) of λ where
      (yes b=b₁) → yes (apⁱ² pi a=a₁ b=b₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ get-abs ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete (def f args) (def f₁ args₁) = caseᵈ (f ＝ⁱ f₁) of λ where
    (yes f=f₁) → case (args-discrete args args₁) return (λ d → Dec (def f args ＝ⁱ def f₁ args₁)) of λ where
      (yes a=a₁) → yes (apⁱ² def f=f₁ a=a₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ get-args ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  term-discrete unknown unknown = yes reflⁱ

  term-discrete (var x args) (con c args₁) = no λ ()
  term-discrete (var x args) (def f args₁) = no λ ()
  term-discrete (var x args) (lam v t) = no λ ()
  term-discrete (var x args) (pat-lam cs args₁) = no λ ()
  term-discrete (var x args) (pi a b) = no λ ()
  term-discrete (var x args) (agda-sort s) = no λ ()
  term-discrete (var x args) (lit l) = no λ ()
  term-discrete (var x args) (meta x₁ x₂) = no λ ()
  term-discrete (var x args) unknown = no λ ()
  term-discrete (con c args) (var x args₁) = no λ ()
  term-discrete (con c args) (def f args₁) = no λ ()
  term-discrete (con c args) (lam v t) = no λ ()
  term-discrete (con c args) (pat-lam cs args₁) = no λ ()
  term-discrete (con c args) (pi a b) = no λ ()
  term-discrete (con c args) (agda-sort s) = no λ ()
  term-discrete (con c args) (lit l) = no λ ()
  term-discrete (con c args) (meta x x₁) = no λ ()
  term-discrete (con c args) unknown = no λ ()
  term-discrete (pat-lam cs args) (var x args₁) = no λ ()
  term-discrete (pat-lam cs args) (con c args₁) = no λ ()
  term-discrete (pat-lam cs args) (def f args₁) = no λ ()
  term-discrete (pat-lam cs args) (lam v t) = no λ ()
  term-discrete (pat-lam cs args) (pi a b) = no λ ()
  term-discrete (pat-lam cs args) (agda-sort s) = no λ ()
  term-discrete (pat-lam cs args) (lit l) = no λ ()
  term-discrete (pat-lam cs args) (meta x x₁) = no λ ()
  term-discrete (pat-lam cs args) unknown = no λ ()
  term-discrete (agda-sort s) (var x args) = no λ ()
  term-discrete (agda-sort s) (con c args) = no λ ()
  term-discrete (agda-sort s) (def f args) = no λ ()
  term-discrete (agda-sort s) (lam v t) = no λ ()
  term-discrete (agda-sort s) (pat-lam cs args) = no λ ()
  term-discrete (agda-sort s) (pi a b) = no λ ()
  term-discrete (agda-sort s) (lit l) = no λ ()
  term-discrete (agda-sort s) (meta x x₁) = no λ ()
  term-discrete (agda-sort s) unknown = no λ ()
  term-discrete (lit l) (var x args) = no λ ()
  term-discrete (lit l) (con c args) = no λ ()
  term-discrete (lit l) (def f args) = no λ ()
  term-discrete (lit l) (lam v t) = no λ ()
  term-discrete (lit l) (pat-lam cs args) = no λ ()
  term-discrete (lit l) (pi a b) = no λ ()
  term-discrete (lit l) (agda-sort s) = no λ ()
  term-discrete (lit l) (meta x x₁) = no λ ()
  term-discrete (lit l) unknown = no λ ()
  term-discrete (meta x x₁) (var x₂ args) = no λ ()
  term-discrete (meta x x₁) (con c args) = no λ ()
  term-discrete (meta x x₁) (def f args) = no λ ()
  term-discrete (meta x x₁) (lam v t) = no λ ()
  term-discrete (meta x x₁) (pat-lam cs args) = no λ ()
  term-discrete (meta x x₁) (pi a b) = no λ ()
  term-discrete (meta x x₁) (agda-sort s) = no λ ()
  term-discrete (meta x x₁) (lit l) = no λ ()
  term-discrete (meta x x₁) unknown = no λ ()
  term-discrete (lam v t) (var x args) = no λ ()
  term-discrete (lam v t) (con c args) = no λ ()
  term-discrete (lam v t) (def f args) = no λ ()
  term-discrete (lam v t) (pat-lam cs args) = no λ ()
  term-discrete (lam v t) (pi a b) = no λ ()
  term-discrete (lam v t) (agda-sort s) = no λ ()
  term-discrete (lam v t) (lit l) = no λ ()
  term-discrete (lam v t) (meta x x₁) = no λ ()
  term-discrete (lam v t) unknown = no λ ()
  term-discrete (pi a b) (var x args) = no λ ()
  term-discrete (pi a b) (con c args) = no λ ()
  term-discrete (pi a b) (def f args) = no λ ()
  term-discrete (pi a b) (lam v t) = no λ ()
  term-discrete (pi a b) (pat-lam cs args) = no λ ()
  term-discrete (pi a b) (agda-sort s) = no λ ()
  term-discrete (pi a b) (lit l) = no λ ()
  term-discrete (pi a b) (meta x x₁) = no λ ()
  term-discrete (pi a b) unknown = no λ ()
  term-discrete (def f args) (var x args₁) = no λ ()
  term-discrete (def f args) (con c args₁) = no λ ()
  term-discrete (def f args) (lam v t) = no λ ()
  term-discrete (def f args) (pat-lam cs args₁) = no λ ()
  term-discrete (def f args) (pi a b) = no λ ()
  term-discrete (def f args) (agda-sort s) = no λ ()
  term-discrete (def f args) (lit l) = no λ ()
  term-discrete (def f args) (meta x x₁) = no λ ()
  term-discrete (def f args) unknown = no λ ()
  term-discrete unknown (var x args) = no λ ()
  term-discrete unknown (con c args) = no λ ()
  term-discrete unknown (def f args) = no λ ()
  term-discrete unknown (lam v t) = no λ ()
  term-discrete unknown (pat-lam cs args) = no λ ()
  term-discrete unknown (pi a b) = no λ ()
  term-discrete unknown (agda-sort s) = no λ ()
  term-discrete unknown (lit l) = no λ ()
  term-discrete unknown (meta x x₁) = no λ ()

  sort-discrete (set t) (set t₁) = case (term-discrete t t₁) return (λ _ → Dec (set t ＝ⁱ set t₁)) of λ where
    (yes t=t₁) → yes (apⁱ set t=t₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  sort-discrete (lit n) (lit n₁) = caseᵈ (n ＝ⁱ n₁) of λ where
    (yes n=n₁) → yes (apⁱ lit n=n₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  sort-discrete (prop t) (prop t₁) = case (term-discrete t t₁) return (λ _ → Dec (prop t ＝ⁱ prop t₁)) of λ where
    (yes t=t₁) → yes (apⁱ prop t=t₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  sort-discrete (prop-lit n) (prop-lit n₁) = caseᵈ (n ＝ⁱ n₁) of λ where
    (yes n=n₁) → yes (apⁱ prop-lit n=n₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  sort-discrete (inf n) (inf n₁) = caseᵈ (n ＝ⁱ n₁) of λ where
    (yes n=n₁) → yes (apⁱ inf n=n₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  sort-discrete unknown unknown = yes reflⁱ

  sort-discrete (set t) (lit n) = no λ ()
  sort-discrete (set t) (prop t₁) = no λ ()
  sort-discrete (set t) (prop-lit n) = no λ ()
  sort-discrete (set t) (inf n) = no λ ()
  sort-discrete (set t) unknown = no λ ()
  sort-discrete (lit n) (set t) = no λ ()
  sort-discrete (lit n) (prop t) = no λ ()
  sort-discrete (lit n) (prop-lit n₁) = no λ ()
  sort-discrete (lit n) (inf n₁) = no λ ()
  sort-discrete (lit n) unknown = no λ ()
  sort-discrete (prop t) (set t₁) = no λ ()
  sort-discrete (prop t) (lit n) = no λ ()
  sort-discrete (prop t) (prop-lit n) = no λ ()
  sort-discrete (prop t) (inf n) = no λ ()
  sort-discrete (prop t) unknown = no λ ()
  sort-discrete (prop-lit n) (set t) = no λ ()
  sort-discrete (prop-lit n) (lit n₁) = no λ ()
  sort-discrete (prop-lit n) (prop t) = no λ ()
  sort-discrete (prop-lit n) (inf n₁) = no λ ()
  sort-discrete (prop-lit n) unknown = no λ ()
  sort-discrete (inf n) (set t) = no λ ()
  sort-discrete (inf n) (lit n₁) = no λ ()
  sort-discrete (inf n) (prop t) = no λ ()
  sort-discrete (inf n) (prop-lit n₁) = no λ ()
  sort-discrete (inf n) unknown = no λ ()
  sort-discrete unknown (set t) = no λ ()
  sort-discrete unknown (lit n) = no λ ()
  sort-discrete unknown (prop t) = no λ ()
  sort-discrete unknown (prop-lit n) = no λ ()
  sort-discrete unknown (inf n) = no λ ()

  clause-discrete (clause tel ps t) (clause tel₁ ps₁ t₁) = case tel-discrete tel tel₁ return (λ _ → Dec (clause tel ps t ＝ⁱ clause tel₁ ps₁ t₁)) of λ where
    (yes tel=tel₁) → case patterns-discrete ps ps₁ return (λ _ → Dec (clause tel ps t ＝ⁱ clause tel₁ ps₁ t₁)) of λ where
      (yes p=p₁) → case term-discrete t t₁ return (λ _ → Dec (clause tel ps t ＝ⁱ clause tel₁ ps₁ t₁)) of λ where
        (yes t=t₁) → yes (apⁱ³ clause tel=tel₁ p=p₁ t=t₁)
        (no ¬qs)   → no λ qs → ¬qs (apⁱ clause→term qs)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ clause→patterns ps)
    (no ¬as)       → no λ { reflⁱ → ¬as reflⁱ }
  clause-discrete (absurd-clause tel ps) (absurd-clause tel₁ ps₁) = case tel-discrete tel tel₁ return (λ _ → Dec (absurd-clause tel ps ＝ⁱ absurd-clause tel₁ ps₁)) of λ where
    (yes tel=tel₁) → case patterns-discrete ps ps₁ return (λ _ → Dec (absurd-clause tel ps ＝ⁱ absurd-clause tel₁ ps₁)) of λ where
      (yes p=p₁) → yes (apⁱ² absurd-clause tel=tel₁ p=p₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ clause→patterns ps)
    (no ¬as)       → no λ { reflⁱ → ¬as reflⁱ }
  clause-discrete (clause tel ps t) (absurd-clause tel₁ ps₁) = no λ()
  clause-discrete (absurd-clause tel ps) (clause tel₁ ps₁ t) = no λ()

  unpats : Pattern → Patterns
  unpats (con c ps) = ps
  unpats _ = []

  pattern-discrete (con c ps) (con c₁ ps₁) = caseᵈ (c ＝ⁱ c₁) of λ where
    (yes c=c₁) → case patterns-discrete ps ps₁ return (λ _ → Dec (con c ps ＝ⁱ con c₁ ps₁)) of λ where
      (yes p=p₁) → yes (apⁱ² con c=c₁ p=p₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ unpats ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  pattern-discrete (dot t) (dot t₁) = case term-discrete t t₁ return (λ _ → Dec (dot t ＝ⁱ dot t₁)) of λ where
    (yes t=t₁) → yes (apⁱ dot t=t₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  pattern-discrete (var x) (var x₁) = caseᵈ (x ＝ⁱ x₁) of λ where
    (yes x=x₁) → yes (apⁱ var x=x₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  pattern-discrete (lit l) (lit l₁) = caseᵈ (l ＝ⁱ l₁) of λ where
    (yes l=l₁) → yes (apⁱ lit l=l₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  pattern-discrete (proj f) (proj f₁) = caseᵈ (f ＝ⁱ f₁) of λ where
    (yes f=f₁) → yes (apⁱ proj f=f₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  pattern-discrete (absurd x) (absurd x₁) = caseᵈ (x ＝ⁱ x₁) of λ where
    (yes x=x₁) → yes (apⁱ absurd x=x₁)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }

  pattern-discrete (con c ps) (dot t) = no λ()
  pattern-discrete (con c ps) (var x) = no λ()
  pattern-discrete (con c ps) (lit l) = no λ()
  pattern-discrete (con c ps) (proj f) = no λ()
  pattern-discrete (con c ps) (absurd x) = no λ()
  pattern-discrete (dot t) (con c ps) = no λ()
  pattern-discrete (dot t) (var x) = no λ()
  pattern-discrete (dot t) (lit l) = no λ()
  pattern-discrete (dot t) (proj f) = no λ()
  pattern-discrete (dot t) (absurd x) = no λ()
  pattern-discrete (var x) (con c ps) = no λ()
  pattern-discrete (var x) (dot t) = no λ()
  pattern-discrete (var x) (lit l) = no λ()
  pattern-discrete (var x) (proj f) = no λ()
  pattern-discrete (var x) (absurd x₁) = no λ()
  pattern-discrete (lit l) (con c ps) = no λ()
  pattern-discrete (lit l) (dot t) = no λ()
  pattern-discrete (lit l) (var x) = no λ()
  pattern-discrete (lit l) (proj f) = no λ()
  pattern-discrete (lit l) (absurd x) = no λ()
  pattern-discrete (proj f) (con c ps) = no λ()
  pattern-discrete (proj f) (dot t) = no λ()
  pattern-discrete (proj f) (var x) = no λ()
  pattern-discrete (proj f) (lit l) = no λ()
  pattern-discrete (proj f) (absurd x) = no λ()
  pattern-discrete (absurd x) (con c ps) = no λ()
  pattern-discrete (absurd x) (dot t) = no λ()
  pattern-discrete (absurd x) (var x₁) = no λ()
  pattern-discrete (absurd x) (lit l) = no λ()
  pattern-discrete (absurd x) (proj f) = no λ()

  -- helpers

  abs-term-discrete (abs s x) (abs s₁ x₁) = caseᵈ (s ＝ⁱ s₁) of λ where
    (yes s=s₁) → case (term-discrete x x₁) return (λ _ → Dec (abs s x ＝ⁱ abs s₁ x₁)) of λ where
      (yes x=x₁) → yes (apⁱ² abs s=s₁ x=x₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ abs-binder ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }

  arg-term-discrete (arg i x) (arg i₁ x₁) = caseᵈ (i ＝ⁱ i₁) of λ where
    (yes i=i₁) → case (term-discrete x x₁) return (λ _ → Dec (arg i x ＝ⁱ arg i₁ x₁)) of λ where
      (yes x=x₁) → yes (apⁱ² arg i=i₁ x=x₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ unarg ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }

  args-discrete [] [] = yes reflⁱ
  args-discrete (x ∷ xs) (y ∷ ys) = case (arg-term-discrete x y) return (λ _ → Dec (x ∷ xs ＝ⁱ y ∷ ys)) of λ where
    (yes x=y) → case (args-discrete xs ys) return (λ _ → Dec (x ∷ xs ＝ⁱ y ∷ ys)) of λ where
      (yes xs=ys) → yes (apⁱ² _∷_ x=y xs=ys)
      (no ¬ps)    → no λ ps → ¬ps (apⁱ tail ps)
    (no ¬as)  → no λ { reflⁱ → ¬as reflⁱ }
  args-discrete [] (x ∷ ys) = no λ()
  args-discrete (x ∷ xs) [] = no λ()

  head′ : Telescope → Arg Term
  head′ [] = arg default-ai unknown
  head′ ((s , t) ∷ ts) = t

  tel-discrete [] [] = yes reflⁱ
  tel-discrete ((s , t) ∷ xs) ((s₁ , t₁) ∷ ys) = caseᵈ (s ＝ⁱ s₁) of λ where
    (yes s=s₁) → case arg-term-discrete t t₁ return (λ _ → Dec ((s , t) ∷ xs ＝ⁱ (s₁ , t₁) ∷ ys)) of λ where
      (yes t=t₁) → case tel-discrete xs ys return (λ _ → Dec ((s , t) ∷ xs ＝ⁱ (s₁ , t₁) ∷ ys)) of λ where
        (yes xs=ys) → yes (apⁱ³ (λ s t xs → (s , t) ∷ xs) s=s₁ t=t₁ xs=ys)
        (no ¬qs)    → no λ qs → ¬qs (apⁱ tail qs)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ head′ ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }
  tel-discrete [] (x ∷ ys) = no λ()
  tel-discrete (x ∷ xs) [] = no λ()

  clauses-discrete [] [] = yes reflⁱ
  clauses-discrete (x ∷ xs) (y ∷ ys) = case (clause-discrete x y) return (λ _ → Dec (x ∷ xs ＝ⁱ y ∷ ys)) of λ where
    (yes x=y) → case (clauses-discrete xs ys) return (λ _ → Dec (x ∷ xs ＝ⁱ y ∷ ys)) of λ where
      (yes xs=ys) → yes (apⁱ² _∷_ x=y xs=ys)
      (no ¬ps)    → no λ ps → ¬ps (apⁱ tail ps)
    (no ¬as)  → no λ { reflⁱ → ¬as reflⁱ }
  clauses-discrete [] (x ∷ ys) = no λ()
  clauses-discrete (x ∷ xs) [] = no λ()

  arg-pattern-discrete (arg i x) (arg i₁ x₁) = caseᵈ (i ＝ⁱ i₁) of λ where
    (yes i=i₁) → case (pattern-discrete x x₁) return (λ _ → Dec (arg i x ＝ⁱ arg i₁ x₁)) of λ where
      (yes x=x₁) → yes (apⁱ² arg i=i₁ x=x₁)
      (no ¬ps)   → no λ ps → ¬ps (apⁱ unarg ps)
    (no ¬as)   → no λ { reflⁱ → ¬as reflⁱ }

  patterns-discrete [] [] = yes reflⁱ
  patterns-discrete (x ∷ xs) (y ∷ ys) = case (arg-pattern-discrete x y) return (λ _ → Dec (x ∷ xs ＝ⁱ y ∷ ys)) of λ where
    (yes x=y) → case (patterns-discrete xs ys) return (λ _ → Dec (x ∷ xs ＝ⁱ y ∷ ys)) of λ where
      (yes xs=ys) → yes (apⁱ² _∷_ x=y xs=ys)
      (no ¬ps)    → no λ ps → ¬ps (apⁱ tail ps)
    (no ¬as)  → no λ { reflⁱ → ¬as reflⁱ }
  patterns-discrete [] (x ∷ ys) = no λ()
  patterns-discrete (x ∷ xs) [] = no λ()

instance
  Term-is-discrete : is-discrete Term
  Term-is-discrete = is-discreteⁱ→is-discrete term-discrete

  Sort-is-discrete : is-discrete Sort
  Sort-is-discrete = is-discreteⁱ→is-discrete sort-discrete

  Pattern-is-discrete : is-discrete Pattern
  Pattern-is-discrete = is-discreteⁱ→is-discrete pattern-discrete

  Clause-is-discrete : is-discrete Clause
  Clause-is-discrete = is-discreteⁱ→is-discrete clause-discrete
