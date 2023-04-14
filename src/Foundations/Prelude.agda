{-# OPTIONS --safe #-}
module Foundations.Prelude where

open import Prim.Type       public
open import Prim.Interval   public
open import Prim.Extension  public
open import Prim.Kan        public
open import Prim.Glue       public

open import Prim.Data.Sigma public
open import Prim.Data.Pi    public
open import Prim.Data.Unit  public

infixr 30 _∙_
infix  3 _∎
infixr 2 _＝⟨_⟩_ _＝⟨⟩_
infixr 2.5 _＝⟨_⟩＝⟨_⟩_
infixl 4 _＝$_ _＝$S_

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : A → Type ℓ
  x y z w : A

Square : {ℓ : Level} {A : Type ℓ} {a00 a01 a10 a11 : A}
         (p : a00 ＝ a01) (q : a00 ＝ a10)
         (s : a01 ＝ a11) (r : a10 ＝ a11)
       → Type ℓ
Square p q s r = ＜ q ／ (λ i → p i ＝ r i) ＼ s ＞

infix 0 Square-syntax
Square-syntax : {ℓ : Level} {A : Type ℓ}
                (d₁ d₂ d₃ d₄ d₅ : ⊤)
                (a₀₀ a₀₁ a₁₀ a₁₁ : A)
                (p : a₀₀ ＝ a₀₁) (q : a₀₀ ＝ a₁₀)
                (s : a₀₁ ＝ a₁₁) (r : a₁₀ ＝ a₁₁)
              → Type ℓ
Square-syntax _ _ _ _ _ _ _ _ _ = Square
-- be not afraid
syntax Square-syntax d₁ d₂ d₃ d₄ d₅ a₀₀ a₀₁ a₁₀ a₁₁ p q s r =
  a₀₀  ̇ q  ̇ a₁₀ ┌─────────┐ d₁ │ d₂ │ p │ d₃ │ r │ d₄ │ d₅ └─────────┘ a₀₁  ̇ s  ̇ a₁₁

-- symP infers the type of its argument from the type of its output
symP : {A : I → Type ℓ} → {x : A i1} → {y : A i0}
       (p : ＜ x    ／ (λ i → A (~ i)) ＼    y ＞)
      →     ＜ y ／    (λ i → A    i )    ＼ x ＞
symP p j = p (~ j)

-- symP infers the type of its output from the type of its argument
symP-from-goal : {A : I → Type ℓ} {x : A i0} {y : A i1}
                 (p : ＜ x    ／ (λ i → A    i ) ＼    y ＞)
               →      ＜ y ／    (λ i → A (~ i))    ＼ x ＞
symP-from-goal p j = p (~ j)

cong-simple : {B : Type ℓ} (f : A → B)
              (p : x ＝ y) → f x ＝ f y
cong-simple f p i = f (p i)
{-# INLINE cong-simple #-}

ap = cong

congP : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
        (f : (i : I) → Π[ a ꞉ A i ] B i a) {x : A i0} {y : A i1}
        (p : ＜      x    ／ (λ i →       A i) ＼         y ＞)
      →      ＜ f i0 x ／ (λ i    →  B i (p i))   ＼ f i1 y ＞
congP f p i = f i (p i)
{-# INLINE congP #-}

cong₂ : {C : Π[ a ꞉ A ] Π[ b ꞉ B a ] Type ℓ}
        (f : Π[ a ꞉ A ] Π[ b ꞉ B a ] C a b)
        (p : x ＝ y) {u : B x} {v : B y}
        (q : ＜     u    ／ (λ i →          B (p i)) ＼        v ＞)
      →      ＜ f x u ／ (λ i    → C (p i) (q    i ))   ＼ f y v ＞
cong₂ f p q i = f (p i) (q i)
{-# INLINE cong₂ #-}

congP₂ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
         {C : (i : I) → Π[ a ꞉ A i ] (B i a → Type ℓ″)}
         (f : (i : I) → Π[ a ꞉ A i ] Π[ b ꞉ B i a ] C i a b)
         {x : A i0} {y : A i1} {u : B i0 x} {v : B i1 y}
         (p : ＜      x         ／ (λ i →      A i)          ＼            y   ＞)
         (q : ＜        u    ／ (λ i    →            B i (p i)) ＼           v ＞)
       →      ＜ f i0 x u ／ (λ i       → C i (p i) (q      i ))   ＼ f i1 y v ＞
congP₂ f p q i = f i (p i) (q i)
{-# INLINE congP₂ #-}

{- Observe an "open box".

        i              x       q i       y
     ∙ —-- >               ┌────────→┐
   j |                     │         │
     v           sym p j   │         │   r j
                           ↓         ↓
                           └         ┘
                       w                 z

-}

-- formal definition of an open box
module _ {A : Type ℓ} {w x y z : A} {p : w ＝ x} {q : x ＝ y} {r : y ＝ z} where private
  double-comp-tube : (i j : I) → Partial (~ i ∨ i ∨ ~ j) A
  double-comp-tube i j (i = i0) = sym p j
  double-comp-tube i j (i = i1) = r j
  double-comp-tube i j (j = i0) = q i

{- The most natural notion of homogenous path composition
    in a cubical setting is double composition:

        i           x        q        y
     ∙ —-- >            ┌────────→┐
   j |                  │         │
     v            p⁻¹   │         │   r
                        ↓         ↓
                        └ ─ ─ ─ -→┘
                    w   p ∙∙ q ∙∙ r   z

   `p ∙∙ q ∙∙ r` gives the line at the bottom,
   `∙∙-filler p q r` gives the whole square.
-}

infix 6 _∙∙_∙∙_
_∙∙_∙∙_ : w ＝ x → x ＝ y → y ＝ z
        → w ＝ z
(p ∙∙ q ∙∙ r) i = hcomp (∂ i) λ where
  j (i = i0) → p (~ j)
  j (i = i1) → r j
  j (j = i0) → q i

∙∙-filler : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
          →   x  ̇      q       ̇ y
                  ┌─────────┐ _
                  │    _    │
          sym p   │    _    │   r
                  │    _    │ _
                  └─────────┘
              w  ̇ p ∙∙ q ∙∙ r  ̇ z
∙∙-filler p q r k i =
  hfill (∂ i) k λ where
    j (i = i0) → p (~ j)
    j (i = i1) → r j
    j (j = i0) → q i

-- any two definitions of double composition are equal
∙∙-unique : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
          → (α β : Σ[ s ꞉ w ＝ z ] Square (sym p) q s r)
          → α ＝ β
∙∙-unique p q r (α , α-fill) (β , β-fill) =
  λ i → (λ j → square i j) , (λ j k → cube i j k)
  where
    cube : (i j : I) → p (~ j) ＝ r j
    cube i j k = hfill (∂ i ∨ ∂ k) j λ where
      l (i = i0) → α-fill l k
      l (i = i1) → β-fill l k
      l (k = i0) → p (~ l)
      l (k = i1) → r l
      l (l = i0) → q k

    square : α ＝ β
    square i j = cube i i1 j

∙∙-contract : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
            → (β : Σ[ s ꞉ w ＝ z ] Square (sym p) q s r)
            → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ＝ β
∙∙-contract p q r β = ∙∙-unique p q r _ β

-- For single homogenous path composition, we take `refl` as the left side:
_∙_ : x ＝ y → y ＝ z → x ＝ z
p ∙ q = refl ∙∙ p ∙∙ q

∙-filler : (p : x ＝ y) (q : y ＝ z)
         →  x  ̇      p       ̇ y
                ┌─────────┐ _
                │    _    │
         refl   │    _    │   q
                │    _    │ _
                └─────────┘
            x  ̇    p ∙ q     ̇ z
∙-filler p q = ∙∙-filler refl p q

∙-unique : {p : x ＝ y} {q : y ＝ z} (r : x ＝ z)
         →  x  ̇      p       ̇ y
                ┌─────────┐ _
                │    _    │
         refl   │    _    │   q
                │    _    │ _
                └─────────┘
            x  ̇      r       ̇ z
         → r ＝ p ∙ q
∙-unique {p} {q} r square i =
  ∙∙-unique refl p q (_ , square) (_ , (∙-filler p q)) i .fst

-- We could have also defined single composition by taking `refl` on the right
infixr 30 _∙′_
_∙′_ : x ＝ y → y ＝ z → x ＝ z
p ∙′ q = p ∙∙ q ∙∙ refl

∙′-filler : (p : x ＝ y) (q : y ＝ z)
         →  y  ̇      q       ̇ z
                ┌─────────┐ _
                │    _    │
        sym p   │    _    │   refl
                │    _    │ _
                └─────────┘
            x  ̇    p ∙′ q    ̇ z
∙′-filler p q = ∙∙-filler p q refl

-- It's easy to show that `p ∙ q` also has such a filler:
∙-filler′ : (p : x ＝ y) (q : y ＝ z)
         →  y  ̇      q       ̇ z
                ┌─────────┐ _
                │    _    │
        sym p   │    _    │   refl
                │    _    │ _
                └─────────┘
            x  ̇    p ∙ q     ̇ z
∙-filler′ p q j i = hcomp (∂ i ∨ ~ j) λ where
  k (i = i0) → p (~ j)
  k (i = i1) → q k
  k (j = i0) → q (i ∧ k)
  k (k = i0) → p (i ∨ ~ j)

-- From this, we can show that these two notions of composition are the same
∙＝∙′ : (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙′ q
∙＝∙′ p q j = ∙∙-unique p q refl (p ∙ q , ∙-filler′ p q) (p ∙′ q , ∙′-filler p q) j .fst

-- Double composition agrees with iterated single composition
∙∙＝∙ : (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
      → p ∙∙ q ∙∙ r ＝ p ∙ q ∙ r
∙∙＝∙ p q r i j = hcomp (i ∨ ∂ j) λ where
  k (i = i1) → ∙-filler′ p (q ∙ r) k j
  k (j = i0) → p (~ k)
  k (j = i1) → r (i ∨ k)
  k (k = i0) → ∙-filler q r i j

-- Or even top side `refl`
infixr 30 _∙″_
_∙″_ : x ＝ y → y ＝ z → x ＝ z
p ∙″ q = p ∙∙ refl ∙∙ q

∙″-filler : (p : x ＝ y) (q : y ＝ z)
          →  y  ̇    refl      ̇ y
                 ┌─────────┐ _
                 │    _    │
         sym p   │    _    │   q
                 │    _    │ _
                 └─────────┘
             x  ̇    p ∙″ q    ̇ z
∙″-filler p q = ∙∙-filler p refl q

∙-filler″ : (p : x ＝ y) (q : y ＝ z)
          →  y  ̇    refl      ̇ y
                 ┌─────────┐ _
                 │    _    │
         sym p   │    _    │   q
                 │    _    │ _
                 └─────────┘
             x  ̇    p ∙ q     ̇ z
∙-filler″ {y} p q j i = hcomp (∂ i ∨ ~ j) λ where
  k (i = i0) → p (~ j)
  k (i = i1) → q (j ∧ k)
  k (j = i0) → y
  k (k = i0) → p (i ∨ ~ j)

∙＝∙″ : (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙″ q
∙＝∙″ p q j = ∙∙-unique p refl q (p ∙ q , ∙-filler″ p q) (p ∙″ q , ∙″-filler p q) j .fst


-- Heterogeneous path composition and its filler:

-- Composition in a family indexed by the interval
infixr 31 _◎_
_◎_
  : {A : I → Type ℓ} {x : A i0} {y : A i1}
    {B1 : Type ℓ} {B : A i1 ＝ B1} {z : B i1}
  → ＜ x    ／ A ＼ y ＞ → ＜ y ／ (λ i → B i) ＼ z ＞
  → ＜ x ／     (λ j → ((λ i → A i) ∙ B) j)       ＼ z ＞
_◎_ {A} {x} {B} p q i = comp (λ j → ∙-filler (λ i → A i) B j i) (∂ i) λ where
  j (i = i0) → x
  j (i = i1) → q j
  j (j = i0) → p i

-- Composition in a family indexed by a type
infixr 32 _◎′_
_◎′_
  : {B : A → Type ℓ′} {x′ : B x} {y′ : B y} {z′ : B z} {p : x ＝ y} {q : y ＝ z}
    (P : ＜ x′    ／ (λ i → B (p i)) ＼ y′ ＞) (Q : ＜ y′ ／ (λ i → B (q i)) ＼ z′ ＞)
  →      ＜ x′ ／                (λ i → B ((p ∙ q) i))                          ＼ z′ ＞
_◎′_ {B} {x′} {p} {q} P Q i = comp (λ j → B (∙-filler p q j i)) (∂ i) λ where
  j (i = i0) → x′
  j (i = i1) → Q j
  j (j = i0) → P i

◎-filler
  : {A : I → Type ℓ} {x : A i0} {y : A i1} {Bi1 : Type ℓ} {B : A i1 ＝ Bi1} {z : B i1}
    (p : ＜ x    ／ A     ＼    y ＞)
    (q : ＜ y ／ (λ i → B i) ＼ z ＞)
  → ＜ p ／ (λ j → PathP (λ k → (∙-filler (λ i → A i) B j k)) x (q j)) ＼ p ◎ q ＞
◎-filler {A} {x} {y} {B} p q j i =
  fill (λ j → ∙-filler (λ i → A i) B j i) (∂ i) j λ where
    k (i = i0) → x
    k (i = i1) → q k
    k (k = i0) → p i

◎′-filler
  : {B : A → Type ℓ′} {x′ : B x} {y′ : B y} {z′ : B z} {p : x ＝ y} {q : y ＝ z}
    (P : ＜ x′ ／ (λ i → B (p i)) ＼ y′ ＞) (Q : ＜ y′ ／ (λ i → B (q i)) ＼ z′ ＞)
  → ＜ P ／ (λ j → PathP (λ i → B (∙-filler p q j i)) x′ (Q j)) ＼ _◎′_ {B = B} P Q ＞
◎′-filler {B} {x′} {p} {q} P Q j i =
  fill (λ j → B (∙-filler p q j i)) (∂ i) j λ where
    k (i = i0) → x′
    k (i = i1) → Q k
    k (k = i0) → P i

-- `cong` has good computational properties:
module _ {B : Type ℓ′} {C : Type ℓ″} {x y : A} where
  module _ {f : A → B} {g : B → C} {p : x ＝ y} where
    cong-comp : cong (g ∘ f) p ＝ cong g (cong f p)
    cong-comp = refl

    cong-id : cong id p ＝ p
    cong-id = refl

    cong-sym : sym (cong f p) ＝ cong f (sym p)
    cong-sym = refl

    cong-refl : cong f (refl {x = x}) ＝ refl
    cong-refl = refl

  cong-comp-∙ : (f : A → B) (p : x ＝ y) (q : y ＝ z) → cong f (p ∙ q) ＝ cong f p ∙ cong f q
  cong-comp-∙ f p q i = ∙∙-unique refl (cong f p) (cong f q)
    (cong f (p ∙ q)      , λ k j → f (∙-filler p q k j))
    (cong f p ∙ cong f q , ∙-filler _ _)
    i .fst


-- Syntax for chains of equational reasoning

_＝⟨_⟩_ : (x : A) → x ＝ y → y ＝ z → x ＝ z
_ ＝⟨ x＝y ⟩ y＝z = x＝y ∙ y＝z

＝⟨⟩-syntax : (x : A) → x ＝ y → y ＝ z → x ＝ z
＝⟨⟩-syntax = _＝⟨_⟩_
infixr 2 ＝⟨⟩-syntax
syntax ＝⟨⟩-syntax x (λ i → B) y = x ＝[ i ]⟨ B ⟩ y

_＝⟨⟩_ : (x : A) → x ＝ y → x ＝ y
_ ＝⟨⟩ x＝y = x＝y

＝⟨⟩⟨⟩-syntax : (x y : A) → x ＝ y → y ＝ z → z ＝ w → x ＝ w
＝⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
infixr 3 ＝⟨⟩⟨⟩-syntax
syntax ＝⟨⟩⟨⟩-syntax x y B C = x ＝⟨ B ⟩＝ y ＝⟨ C ⟩＝

_＝⟨_⟩＝⟨_⟩_ : (x : A) → x ＝ y → y ＝ z → z ＝ w → x ＝ w
_ ＝⟨ x＝y ⟩＝⟨ y＝z ⟩ z＝w = x＝y ∙∙ y＝z ∙∙ z＝w

_∎ : (x : A) → x ＝ x
_ ∎ = refl

along : {A : I → Type ℓ} {x : A i0} {y : A i1}
      → (i : I) → ＜ x ／ A ＼ y ＞
      → A i
along i p = p i

-- Transport and subst

-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transport-refl : (x : A) → transport refl x ＝ x
transport-refl {A} x i = transp (λ _ → A) i x

transport-filler : {A B : Type ℓ} (p : A ＝ B) (x : A)
                 → ＜ x ／ (λ i → p i) ＼ transport p x ＞
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

transport-filler-ext : {A B : Type ℓ} (p : A ＝ B)
                     → ＜ id ／ (λ i → A → p i) ＼ transport p ＞
transport-filler-ext p i x = transport-filler p x i

transport⁻-filler-ext : {A B : Type ℓ} (p : A ＝ B)
                      → ＜ id ／ (λ i → p i → A) ＼ transport (sym p) ＞
transport⁻-filler-ext p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport⁻transport : {A B : Type ℓ} (p : A ＝ B) (a : A)
                    → transport (sym p) (transport p a) ＝ a
transport⁻transport p a i =
  transport⁻-filler-ext p (~ i) (transport-filler-ext p (~ i) a)

-- We want B to be explicit in subst
subst : (B : A → Type ℓ′) (p : x ＝ y) → B x → B y
subst B p = transport (λ i → B (p i))

subst₂ : {B : Type ℓ′} {z w : B} (C : A → B → Type ℓ″)
         (p : x ＝ y) (q : z ＝ w) → C x z → C y w
subst₂ B p q = transport (λ i → B (p i) (q i))

subst-refl : {B : A → Type ℓ} {x : A} (px : B x) → subst B refl px ＝ px
subst-refl = transport-refl

subst-filler : (B : A → Type ℓ′) (p : x ＝ y) (b : B x)
             → ＜ b ／ (λ i → B (p i)) ＼ subst B p b ＞
subst-filler B p = transport-filler (cong B p)

subst₂-filler : {B : Type ℓ′} {z w : B} (C : A → B → Type ℓ″)
                (p : x ＝ y) (q : z ＝ w) (c : C x z)
              → ＜ c ／ (λ i → C (p i) (q i)) ＼ subst₂ C p q c ＞
subst₂-filler C p q = transport-filler (cong₂ C p q)


-- Function extensionality

fun-ext : {B : A → I → Type ℓ′}
          {f : Π[ x ꞉ A ] B x i0} {g : Π[ x ꞉ A ] B x i1}
        → (Π[ x ꞉ A ] ＜ f x    ／                B x  ＼    g x ＞)
        →             ＜ f   ／ (λ i → Π[ x ꞉ A ] B x i)  ＼ g   ＞
fun-ext p i x = p x i

implicit-fun-ext : {B : A → I → Type ℓ′}
                   {f : {x : A} → B x i0} {g : {x : A} → B x i1}
                 → ({x : A} → ＜ f {x} ／               B x ＼    g {x} ＞)
                 →            ＜ f  ／ (λ i → {x : A} → B x i) ＼ g     ＞
implicit-fun-ext p i {x} = p {x} i

-- the inverse to funExt (see Functions.FunExtEquiv), converting paths
-- between functions to homotopies; `funExt⁻` is called `happly` and
-- defined by path induction in the HoTT book (see function 2.9.2 in
-- section 2.9)
fun-ext⁻ : {B : A → I → Type ℓ′}
           {f : Π[ x ꞉ A ] B x i0} {g : Π[ x ꞉ A ] B x i1}
         →            ＜ f      ／ (λ i → Π[ x ꞉ A ] B x i) ＼    g   ＞
         → Π[ x ꞉ A ] ＜ f x ／                      B x       ＼ g x ＞
fun-ext⁻ eq x i = eq i x

happly = fun-ext⁻
_＝$_ = fun-ext⁻

implicit-fun-ext⁻ : {B : A → I → Type ℓ′}
                    {f : {x : A} → B x i0} {g : {x : A} → B x i1}
                  →           ＜ f        ／ (λ i → {x : A} → B x i) ＼    g     ＞
                  → {x : A} → ＜ f {x} ／                     B x       ＼ g {x} ＞
implicit-fun-ext⁻ eq {x} i = eq i {x}

fun-ext-simple⁻ : {B : I → Type ℓ′}
                  {f : A → B i0} {g : A → B i1}
                →            ＜ f      ／ (λ i → Π[ x ꞉ A ] B i) ＼    g   ＞
                → Π[ x ꞉ A ] ＜ f x ／ (λ i    →            B i)    ＼ g x ＞
fun-ext-simple⁻ eq x i = eq i x

_＝$S_ = fun-ext-simple⁻
happly-simple = fun-ext-simple⁻

homotopy-natural : {A : Type ℓ} {B : Type ℓ′}
                 → {f g : A → B}
                 → (H : (x : A) → f x ＝ g x)
                 → {x y : A} (p : x ＝ y)
                 → H x ∙ cong g p ＝ cong f p ∙ H y
homotopy-natural {f} {g} H {x} {y} p = ∙-unique _ λ i j →
  hcomp (~ i ∨ ∂ j) λ where
    k (k = i0) → H x (j ∧ i)
    k (i = i0) → f (p (j ∧ k))
    k (j = i0) → f x
    k (j = i1) → H (p k) i


-- Direct definitions of lower h-levels

is-contr : Type ℓ → Type ℓ
is-contr A = Σ[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y)

is-contr⁻ : Type ℓ → Type ℓ
is-contr⁻ A = Σ[ x ꞉ A ] Π[ y ꞉ A ] (y ＝ x)

is-prop : Type ℓ → Type ℓ
is-prop A = Π[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y)

is-set : Type ℓ → Type ℓ
is-set A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-prop (x ＝ y)

is-groupoid : Type ℓ → Type ℓ
is-groupoid A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-set (x ＝ y)

is-2-groupoid : Type ℓ → Type ℓ
is-2-groupoid A = Π[ x ꞉ A ] Π[ y ꞉ A ] is-groupoid (x ＝ y)


-- Singleton contractibility

fibre : {A : Type ℓ} {B : Type ℓ′} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ′)
fibre {A} f y = Σ[ x ꞉ A ] (f x ＝ y)

SingletonP : (A : I → Type ℓ) (a : A i0) → Type _
SingletonP A a = Σ[ x ꞉ A i1 ] ＜ a ／ A ＼ x ＞

SingletonP⁻ : (A : I → Type ℓ) (a : A i1) → Type _
SingletonP⁻ A a = Σ[ x ꞉ A i0 ] ＜ x ／ A ＼ a ＞

Singleton : {A : Type ℓ} → A → Type _
Singleton {A} = SingletonP (λ _ → A)

Singleton⁻ : {A : Type ℓ} → A → Type _
Singleton⁻ {A} = SingletonP⁻ (λ _ → A)

Singleton-is-prop : {A : Type ℓ} {a : A} (s : Singleton a)
                  → (a , refl) ＝ s
Singleton-is-prop (_ , path) i = path i , square i where
    square : Square refl refl path path
    square i j = path (i ∧ j)

Singleton⁻-is-prop : {A : Type ℓ} {a : A} (s : Singleton⁻ a)
                   → (a , refl) ＝ s
Singleton⁻-is-prop (_ , path) i = path (~ i) , square (~ i) where
    square : Square path path refl refl
    square i j = path (i ∨ j)

Singleton-is-contr : {A : Type ℓ} {a : A} (s : Singleton a)
                   → is-contr (Singleton a)
Singleton-is-contr {a} _ = (a , refl) , Singleton-is-prop

Singleton-is-contr⁻ : {A : Type ℓ} {a : A} (s : Singleton a)
                   → is-contr⁻ (Singleton a)
Singleton-is-contr⁻ {a} _ = (a , refl) , sym ∘ Singleton-is-prop

Singleton⁻-is-contr : {A : Type ℓ} {a : A} (s : Singleton⁻ a)
                    → is-contr (Singleton⁻ a)
Singleton⁻-is-contr {a} _ = (a , refl) , Singleton⁻-is-prop

-- TODO rephrase as map on snd
Singleton⁻-is-contr⁻ : {A : Type ℓ} {a : A} (s : Singleton⁻ a)
                    → is-contr⁻ (Singleton⁻ a)
Singleton⁻-is-contr⁻ {a} _ = (a , refl) , sym ∘ Singleton⁻-is-prop

SingletonP-is-contr : (A : I → Type ℓ) (a : A i0) → is-contr (SingletonP A a)
SingletonP-is-contr A a .fst = _ , transport-filler (λ i → A i) a
SingletonP-is-contr A a .snd (x , p) i = _ , λ j → fill A (∂ i) j λ where
  k (i = i0) → transport-filler (λ i → A i) a k
  k (i = i1) → p k
  k (k = i0) → a


-- Path induction (J) and its computation rule

module _ (P : ∀ y → x ＝ y → Type ℓ′) (d : P x refl) where

  J : (p : x ＝ y) → P y p
  J {y} p = transport (λ i → P (path i .fst) (path i .snd)) d
    where path : (x , refl) ＝ (y , p)
          path = Singleton-is-contr (y , p) .snd _

  J-refl : J refl ＝ d
  J-refl = transport-refl d

  J-∙ : (p : x ＝ y) (q : y ＝ z)
      → J (p ∙ q) ＝ transport (λ i → P (q i) (λ j → ∙-filler p q i j)) (J p)
  J-∙ p q k =
    transp
      (λ i → P (q (i ∨ ~ k))
      (λ j → ∙-filler p q (i ∨ ~ k) j)) (~ k)
      (J (λ j → ∙-filler p q (~ k) j))

-- Multi-variable versions of J
module _ {b : B x}
  (P : (y : A) (p : x ＝ y) (z : B y) (q : ＜ b ／ (λ i → B (p i)) ＼ z ＞) → Type ℓ″)
  (d : P _ refl _ refl) where

  J-dep : {y : A} (p : x ＝ y) {z : B y} (q : ＜ b ／ (λ i → B (p i)) ＼ z ＞) → P _ p _ q
  J-dep _ q = transport (λ i → P _ _ _ (λ j → q (i ∧ j))) d

  J-dep-refl : J-dep refl refl ＝ d
  J-dep-refl = transport-refl d

module _ {x : A}
  {P : (y : A) → x ＝ y → Type ℓ′} {d : (y : A) (p : x ＝ y) → P y p}
  (Q : (y : A) (p : x ＝ y) (z : P y p) → d y p ＝ z → Type ℓ″)
  (r : Q _ refl _ refl) where

  private
    ΠQ : (y : A) → x ＝ y → _
    ΠQ y p = ∀ z q → Q y p z q

  J₂ : {y : A} (p : x ＝ y) {z : P y p} (q : d y p ＝ z) → Q _ p _ q
  J₂ p = J ΠQ (λ _ → J (Q x refl) r) p _

  J₂-refl : J₂ refl refl ＝ r
  J₂-refl = (λ i → J-refl ΠQ (λ _ → J (Q x refl) r) i _ refl) ∙ J-refl (Q x refl) _

-- A prefix operator version of J that is more suitable to be nested

module _ {P : ∀ y → x ＝ y → Type ℓ′} (d : P x refl) where

  J>_ : ∀ y → (p : x ＝ y) → P y p
  J>_ _ p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  infix 10 J>_


-- Squeezing and spreading, coercions

I-eq : I → I → I
I-eq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

-- interval interpolation function
I-interp : I → I → I → I
I-interp t x y = (~ t ∧ x) ∨ (t ∧ y) ∨ (x ∧ y)

module _ {ℓ^ : I → Level} (A : (i : I) → Type (ℓ^ i)) where
  coe : (i j : I) → A i → A j
  coe i j = transp (λ k → A (I-interp k i j)) (I-eq i j)

  -- forward spread
  coe0→i : (i : I) → A i0 → A i
  coe0→i i = coe i0 i -- transp (λ j → A (i ∧ j)) (~ i)

  -- backward spread
  coe1→i : (i : I) → A i1 → A i
  coe1→i i = coe i1 i -- transp (λ j → A (i ∨ ~ j)) i

  -- backward squeeze
  coei→0 : (i : I) → A i → A i0
  coei→0 i = coe i i0  -- transp (λ j → A (i ∧ ~ j)) (~ i)

  -- forward squeeze
  coei→1 : (i : I) → A i → A i1
  coei→1 i = coe i i1  -- transp (λ l → A (i ∨ l)) i

module _ (A : I → Type ℓ) where
  -- forward transport
  coe0→1 : A i0 → A i1
  coe0→1 = coei→1 A i0 -- transp (λ i → A i) i0

  -- backward transport
  coe1→0 : A i1 → A i0
  coe1→0 = coei→0 A i1 -- transp (λ i → A (~ i)) i0

  -- Observe the computational behaviour of `coe`!
  private
    coei0→0 : (a : A i0) → coei→0 A i0 a ＝ a
    coei0→0 _ = refl

    coei1→0 : (a : A i1) → coei→0 A i1 a ＝ coe1→0 a
    coei1→0 _ = refl

    coei0→1 : (a : A i0) → coei→1 A i0 a ＝ coe0→1 a
    coei0→1 _ = refl

    coei1→1 : (a : A i1) → coei→1 A i1 a ＝ a
    coei1→1 _ = refl

  coei→i : (i : I) (x : A i) → coe A i i x ＝ x
  coei→i i x j = transp (λ _ → A i) (j ∨ i ∨ ~ i) x

  coe-path : (p : (i : I) → A i) (i j : I) → coe A i j (p i) ＝ p j
  coe-path p i j k = transp
    (λ l → A (I-interp k (I-interp l i j) j))
    (I-interp k (I-eq i j) i1)
    (p (I-interp k i j))


-- Converting to and from a PathP

PathP＝Path : (P : I → Type ℓ) (p : P i0) (q : P i1)
            → ＜ p ／ P ＼ q ＞ ＝ (transport (λ i → P i) p ＝ q)
PathP＝Path P p q i =
  ＜ transport-filler (λ j → P j) p i ／ (λ j → P (i ∨ j)) ＼ q ＞

PathP＝Path⁻ : (P : I → Type ℓ) (p : P i0) (q : P i1)
             → ＜ p ／ P ＼  q ＞ ＝ (p ＝ transport (λ i → P (~ i)) q)
PathP＝Path⁻ P p q i =
  ＜ p ／ (λ j → P (~ i ∧ j)) ＼ transport-filler (λ j → P (~ j)) q i ＞



module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  -- to-PathP : (transport (λ i → A i) x ＝ y) → ＜ x ／ A ＼ y ＞
  to-PathP : (coe0→1 A x ＝ y) → ＜ x ／ A ＼ y ＞
  to-PathP p i = hcomp (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe0→i A i x

  -- fromPathP : ＜ x ／ A ＼ y ＞ → transport (λ i → A i) x ＝ y
  from-PathP : ＜ x ／ A ＼ y ＞ → coe0→1 A x ＝ y
  from-PathP p i = transp (λ j → A (i ∨ j)) i (p i)

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  to-PathP⁻ : x ＝ coe1→0 A y → ＜ x ／ A ＼ y ＞
  to-PathP⁻ p = symP $ to-PathP {A = λ j → A (~ j)} (λ i → p (~ i))

  from-PathP⁻ : ＜ x ／ A ＼ y ＞ → x ＝ coe1→0 A y
  from-PathP⁻ p = sym $ from-PathP (λ i → p (~ i))

  to-from-PathP : (p : ＜ x ／ A ＼ y ＞) → to-PathP (from-PathP p) ＝ p
  to-from-PathP p i j = hcomp-unique (∂ j)
    (λ { k (k = i0) → coe0→i A j x
       ; k (j = i0) → x
       ; k (j = i1) → coei→1 A k (p k)
     })
    (λ k → inS (transp (λ l → A (j ∧ (k ∨ l))) (~ j ∨ k) (p (j ∧ k))))
    i

  -- just pray
  from-to-PathP : (p : coe0→1 A x ＝ y) → from-PathP {A = A} (to-PathP p) ＝ p
  from-to-PathP p i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) →
          coei→1 A (j ∨ ~ i) $
            transp (λ l → A (j ∨ (~ i ∧ l))) (i ∨ j) $
                   coe0→i A j x

      k (j = i0) → slide (k ∨ ~ i)
      k (j = i1) → p k

      k (i = i0) → coei→1 A j $ hfill (∂ j) k λ where
        k (k = i0) → coe0→i A j x
        k (j = i0) → x
        k (j = i1) → p k

      k (i = i1) → hcomp (∂ k ∨ ∂ j) λ where
        l (l = i0) → slide (k ∨ j)
        l (k = i0) → slide j
        l (k = i1) → p (j ∧ l)
        l (j = i0) → slide k
        l (j = i1) → p (k ∧ l)
    where
      slide : coe0→1 A x ＝ coe0→1 A x
      slide i = coei→1 A i (coe0→i A i x)


-- Sigma path space
Σ-PathP : {A : Type ℓ} {B : A → Type ℓ′}
        → {x y : Σ A B}
        → (p :              x .fst ＝ y .fst                 )
        →   ＜ x .snd ／     (λ i → B (p i))    ＼ y .snd ＞
        → x ＝ y
Σ-PathP p q i = p i , q i

Σ-Path : {A : Type ℓ} {B : A → Type ℓ′}
       → {x y : Σ A B}
       → (p : x .fst ＝ y .fst)
       → subst B p (x .snd) ＝ (y .snd)
       → x ＝ y
Σ-Path p q = Σ-PathP p (to-PathP q)


-- Path transport

double-composite
  : (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
  → p ∙∙ q ∙∙ r ＝ p ∙ q ∙ r
double-composite p q r i j =
  hcomp (i ∨ ∂ j) λ where
    k (i = i1) → ∙-filler′ p (q ∙ r) k j
    k (j = i0) → p (~ k)
    k (j = i1) → r (i ∨ k)
    k (k = i0) → ∙-filler q r i j

transport-path : {x y x′ y′ : A}
               → (p : x ＝ y)
               → (left : x ＝ x′) → (right : y ＝ y′)
               → transport (λ i → left i ＝ right i) p ＝ sym left ∙ p ∙ right
transport-path {A} p left right = lemma ∙ double-composite _ _ _
  where
  lemma : _ ＝ (sym left ∙∙ p ∙∙ right)
  lemma i j = hcomp (~ i ∨ ∂ j) λ where
    k (k = i0) → transp (λ j → A) i (p j)
    k (i = i0) → hfill (∂ j) k λ where
      k (k = i0) → transp (λ i → A) i0 (p j)
      k (j = i0) → transp (λ j → A) k (left k)
      k (j = i1) → transp (λ j → A) k (right k)
    k (j = i0) → transp (λ j → A) (k ∨ i) (left k)
    k (j = i1) → transp (λ j → A) (k ∨ i) (right k)

subst-path-left : {x y x′ : A}
                → (p : x ＝ y)
                → (left : x ＝ x′)
                → subst (λ e → e ＝ y) left p ＝ sym left ∙ p
subst-path-left {y} p left =
  subst (λ e → e ＝ y) left p     ＝⟨⟩
  transport (λ i → left i ＝ y) p ＝⟨ transport-path p left refl ⟩
  sym left ∙ p ∙ refl             ＝⟨ cong (sym left ∙_) (sym (∙-filler _ _)) ⟩
  sym left ∙ p                    ∎

subst-path-right : {x y y′ : A}
                 → (p : x ＝ y)
                 → (right : y ＝ y′)
                 → subst (λ e → x ＝ e) right p ＝ p ∙ right
subst-path-right {x} p right =
  subst (λ e → x ＝ e) right p     ＝⟨⟩
  transport (λ i → x ＝ right i) p ＝⟨ transport-path p refl right ⟩
  sym refl ∙ p ∙ right             ＝⟨⟩
  refl ∙ p ∙ right                 ＝⟨ sym (∙-filler′ _ _) ⟩
  p ∙ right                        ∎

subst-path-both : {x x′ : A}
                → (p : x ＝ x)
                → (adj : x ＝ x′)
                → subst (λ x → x ＝ x) adj p ＝ sym adj ∙ p ∙ adj
subst-path-both p adj = transport-path p adj adj


-- TODO Move to another file?
-- Whiskering a dependent path by a path

-- Double whiskering
infix 8 _◁_▷_
_◁_▷_ : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ a₁′ : A i1}
      →    a₀ ＝ a₀′ → ＜ a₀′ ／ A ＼ a₁ ＞ → a₁ ＝ a₁′
      → ＜ a₀              ／    A    ＼            a₁′ ＞
(p ◁ P ▷ q) i = hcomp (∂ i) λ where
  j (i = i0) → p (~ j)
  j (i = i1) → q j
  j (j = i0) → P i

double-whiskering-filler
  : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ a₁′ : A i1}
  → (p : a₀ ＝ a₀′) (pq : PathP A a₀′ a₁) (q : a₁ ＝ a₁′)
  → ＜ pq ／ (λ i → ＜ p (~ i) ／ A ＼ q i ＞) ＼ p ◁ pq ▷ q ＞
--→ ＜ pq ／ (λ i → PathP A (p (~ i)) (q i)) ＼ p ◁ pq ▷ q ＞
double-whiskering-filler p pq q k i = hfill (∂ i) k λ where
  j (i = i0) → p (~ j)
  j (i = i1) → q j
  j (j = i0) → pq i

infix 24 _◁_
_◁_ : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ : A i1}
    →    a₀ ＝ a₀′ → ＜ a₀′ ／ A ＼    a₁ ＞
    → ＜ a₀              ／    A    ＼ a₁ ＞
(p ◁ q) = p ◁ q ▷ refl

infix 24 _▷_
_▷_ : {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁′ : A i1}
    → ＜ a₀    ／ A ＼ a₁ ＞ → a₁ ＝ a₁′
    → ＜ a₀ ／    A    ＼            a₁′ ＞
p ▷ q  = refl ◁ p ▷ q


-- TODO Move to another file?
-- Higher cube types

-- Square : {ℓ : Level} {A : Type ℓ} {a00 a01 a10 a11 : A}
--          (p : a00 ＝ a01) (q : a00 ＝ a10)
--          (s : a01 ＝ a11) (r : a10 ＝ a11)
--        → Type ℓ
-- Square p q s r = ＜ q ／ (λ i → p i ＝ r i) ＼ s ＞

SquareP
  : (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : ＜ a₀₀ ／ (λ j → A i0 j) ＼ a₀₁ ＞)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : ＜ a₁₀ ／ (λ j → A i1 j) ＼ a₁₁ ＞)
    (a₋₀ : ＜ a₀₀ ／ (λ i → A i i0) ＼ a₁₀ ＞) (a₋₁ : ＜ a₀₁ ／ (λ i → A i i1) ＼ a₁₁ ＞)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = ＜ a₀₋ ／ (λ i → ＜ a₋₀ i ／ (λ j → A i j) ＼ a₋₁ i ＞) ＼ a₁₋ ＞

-- Cube :
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ＝ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ＝ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ＝ a₀₁₀} {a₀₋₁ : a₀₀₁ ＝ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ＝ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ＝ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ＝ a₁₁₀} {a₁₋₁ : a₁₀₁ ＝ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ＝ a₁₀₀} {a₋₀₁ : a₀₀₁ ＝ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ＝ a₁₁₀} {a₋₁₁ : a₀₁₁ ＝ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   → Type _
-- Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
--   PathP (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋


-- TODO Move to another file
-- Horizontal composition of squares (along their second dimension)
-- See Cubical.Foundations.Path for vertical composition

-- infixr 30 _∙₂_
-- _∙₂_ :
--   {a₀₀ a₀₁ a₀₂ : A} {a₀₋ : a₀₀ ＝ a₀₁} {b₀₋ : a₀₁ ＝ a₀₂}
--   {a₁₀ a₁₁ a₁₂ : A} {a₁₋ : a₁₀ ＝ a₁₁} {b₁₋ : a₁₁ ＝ a₁₂}
--   {a₋₀ : a₀₀ ＝ a₁₀} {a₋₁ : a₀₁ ＝ a₁₁} {a₋₂ : a₀₂ ＝ a₁₂}
--   (p : Square a₀₋ a₁₋ a₋₀ a₋₁) (q : Square b₀₋ b₁₋ a₋₁ a₋₂)
--   → Square (a₀₋ ∙ b₀₋) (a₁₋ ∙ b₁₋) a₋₀ a₋₂
-- _∙₂_ = congP₂ (λ _ → _∙_)


-- TODO Move to another file
-- Alternative (equivalent) definitions of hlevel n that give fillers for n-cubes instead of n-globes

-- isSet' : Type ℓ → Type ℓ
-- isSet' A =
--   {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ＝ a₀₁)
--   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ＝ a₁₁)
--   (a₋₀ : a₀₀ ＝ a₁₀) (a₋₁ : a₀₁ ＝ a₁₁)
--   → Square a₀₋ a₁₋ a₋₀ a₋₁

-- isSet→isSet' : isSet A → isSet' A
-- isSet→isSet' Aset _ _ _ _ = toPathP (Aset _ _ _ _)

-- isSet'→isSet : isSet' A → isSet A
-- isSet'→isSet Aset' x y p q = Aset' p q refl refl

-- isGroupoid' : Type ℓ → Type ℓ
-- isGroupoid' A =
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ＝ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ＝ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ＝ a₀₁₀} {a₀₋₁ : a₀₀₁ ＝ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ＝ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ＝ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ＝ a₁₁₀} {a₁₋₁ : a₁₀₁ ＝ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ＝ a₁₀₀} {a₋₀₁ : a₀₀₁ ＝ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ＝ a₁₁₀} {a₋₁₁ : a₀₁₁ ＝ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁


-- TODO uncomment
-- Essential properties of isProp and isContr

-- isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) → isProp (B i))
--                → (b0 : B i0) (b1 : B i1)
--                → PathP B b0 b1
-- isProp→PathP hB b0 b1 = toPathP (hB _ _ _)

-- isPropIsContr : isProp (isContr A)
-- isPropIsContr (c0 , h0) (c1 , h1) j .fst = h0 c1 j
-- isPropIsContr (c0 , h0) (c1 , h1) j .snd y i =
--    hcomp (λ k → λ { (i = i0) → h0 (h0 c1 j) k;
--                     (i = i1) → h0 y k;
--                     (j = i0) → h0 (h0 y i) k;
--                     (j = i1) → h0 (h1 y i) k})
--          c0

-- isContr→isProp : isContr A → isProp A
-- isContr→isProp (x , p) a b = sym (p a) ∙ p b

-- isProp→isSet : isProp A → isSet A
-- isProp→isSet h a b p q j i =
--   hcomp (λ k → λ { (i = i0) → h a a k
--                  ; (i = i1) → h a b k
--                  ; (j = i0) → h a (p i) k
--                  ; (j = i1) → h a (q i) k }) a

-- isProp→isSet' : isProp A → isSet' A
-- isProp→isSet' h {a} p q r s i j =
--   hcomp (λ k → λ { (i = i0) → h a (p j) k
--                  ; (i = i1) → h a (q j) k
--                  ; (j = i0) → h a (r i) k
--                  ; (j = i1) → h a (s i) k}) a

-- isPropIsProp : isProp (isProp A)
-- isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

-- isPropSingl : {a : A} → isProp (singl a)
-- isPropSingl = isContr→isProp (isContrSingl _)

-- isPropSinglP : {A : I → Type ℓ} {a : A i0} → isProp (singlP A a)
-- isPropSinglP = isContr→isProp (isContrSinglP _ _)


-- TODO refactor
-- -- Universe lifting
-- liftExt : ∀ {A : Type ℓ} {a b : Lift {ℓ} {ℓ'} A} → (lower a ＝ lower b) → a ＝ b
-- liftExt x i = lift (x i)

-- onAllPaths : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
-- onAllPaths S A = (x y : A) → S (x ＝ y)
