
{-# OPTIONS --safe #-}
module Foundations.Base where

open import Foundations.Prim.Type       public
open import Foundations.Prim.Interval   public
open import Foundations.Prim.Extension  public
open import Foundations.Prim.Kan        public
open import Foundations.Prim.Glue       public

open import Agda.Builtin.Nat
  using (zero; suc)
  renaming (Nat to ℕ)
open import Agda.Builtin.Unit      public
open import Foundations.Pi.Base    public
open import Foundations.Sigma.Base public


infixr 30 _∙_
infix  3 _∎
infixr 2 _＝⟨_⟩_ _＝˘⟨_⟩_ _＝⟨⟩_
infixr 2.5 _＝⟨_⟩＝⟨_⟩_

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : A → Type ℓ′
  x y z w : A

lift-ext : {a b : Lift {ℓ} ℓ′ A} → (lower a ＝ lower b) → a ＝ b
lift-ext x i = lift (x i)

Square : {a₀₀ a₀₁ : A} (p : a₀₀ ＝ a₀₁)
         {a₁₀ : A} (q : a₀₀ ＝ a₁₀)
         {a₁₁ : A} (r : a₁₀ ＝ a₁₁) (s : a₀₁ ＝ a₁₁)
       → Type (level-of-type A)
Square p q r s = ＜ q ／ (λ j → p j ＝ r j) ＼ s ＞

infix 0 Square-syntax
Square-syntax : (d : ⊤)
                (a₀₀ a₀₁ a₁₀ a₁₁ : A)
                (p : a₀₀ ＝ a₀₁) (q : a₀₀ ＝ a₁₀)
                (r : a₁₀ ＝ a₁₁) (s : a₀₁ ＝ a₁₁)
              → Type (level-of-type A)
Square-syntax _ _ _ _ _ p q r s = Square p q r s
-- be not afraid
syntax Square-syntax d a₀₀ a₀₁ a₁₀ a₁₁ p q r s =
  a₀₀  ̇ q  ̇ a₁₀ ┌─  ̇ ─┐ p │ d │ r └─  ̇ ─┘ a₀₁  ̇ s  ̇ a₁₁

private variable
  p : w ＝ x
  q : x ＝ y
  r : y ＝ z
  s : w ＝ z

-- symP infers the type of its argument from the type of its output
symP : {A : I → Type ℓ} {x : A i1} {y : A i0}
       (p : ＜ x    ／ (λ i → A (~ i)) ＼    y ＞)
     →      ＜ y ／    (λ i → A    i )    ＼ x ＞
symP p j = p (~ j)

-- symP infers the type of its output from the type of its argument
symP-from-goal : {A : I → Type ℓ} {x : A i0} {y : A i1}
                 (p : ＜ x    ／ (λ i → A    i ) ＼    y ＞)
               →      ＜ y ／    (λ i → A (~ i))    ＼ x ＞
symP-from-goal p j = p (~ j)

ap-simple : {B : Type ℓ′} (f : A → B)
            (p : x ＝ y) → f x ＝ f y
ap-simple f p i = f (p i)
{-# INLINE ap-simple #-}


apP : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
      (f : (i : I) → Π[ a ꞉ A i ] B i a) {x : A i0} {y : A i1}
      (p : ＜      x    ／ (λ i →       A i) ＼         y ＞)
    →      ＜ f i0 x ／ (λ i    →  B i (p i))   ＼ f i1 y ＞
apP f p i = f i (p i)
{-# INLINE apP #-}

ap² : {C : Π[ a ꞉ A ] Π[ b ꞉ B a ] Type ℓ}
      (f : Π[ a ꞉ A ] Π[ b ꞉ B a ] C a b)
      (p : x ＝ y) {u : B x} {v : B y}
      (q : ＜     u    ／ (λ i →          B (p i)) ＼        v ＞)
    →      ＜ f x u ／ (λ i    → C (p i) (q    i ))   ＼ f y v ＞
ap² f p q i = f (p i) (q i)
{-# INLINE ap² #-}

apP² : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
       {C : (i : I) → Π[ a ꞉ A i ] (B i a → Type ℓ″)}
       (f : (i : I) → Π[ a ꞉ A i ] Π[ b ꞉ B i a ] C i a b)
       {x : A i0} {y : A i1} {u : B i0 x} {v : B i1 y}
       (p : ＜      x         ／ (λ i →      A i)          ＼            y   ＞)
       (q : ＜        u    ／ (λ i    →            B i (p i)) ＼           v ＞)
     →      ＜ f i0 x u ／ (λ i       → C i (p i) (q      i ))   ＼ f i1 y v ＞
apP² f p q i = f i (p i) (q i)
{-# INLINE apP² #-}

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
module _ {w x y z : A} {p : w ＝ x} {q : x ＝ y} {r : y ＝ z} where private
  double-comp-tube : (i j : I) → Partial (∂ i ∨ ~ j) A
  double-comp-tube i j (i = i0) = sym p j
  double-comp-tube i j (i = i1) = r j
  double-comp-tube i j (j = i0) = q i

{- The most natural notion of homogenous path composition
    in a cubical setting is double composition:

        i           x        q        y
     ∙ ---→             ┌────────→┐
   j ∣                  │         │
     ↓            p⁻¹   │         │   r
                        ↓         ↓
                        └ ─ ─ ─ -→┘
                    w   p ∙∙ q ∙∙ r   z

   `p ∙∙ q ∙∙ r` gives the line at the bottom,
   `∙∙-filler p q r` gives the whole square.
-}

opaque
  infix 6 _∙∙_∙∙_
  _∙∙_∙∙_ : w ＝ x → x ＝ y → y ＝ z
          → w ＝ z
  (p ∙∙ q ∙∙ r) i = hcomp (∂ i) λ where
    j (i = i0) → p (~ j)
    j (i = i1) → r j
    j (j = i0) → q i

  ∙∙-filler : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
            →   x  ̇       q        ̇ y
                    ┌─     ̇    ─┐

            sym p   │     _     │   r

                    └─     ̇    ─┘
                w  ̇  p ∙∙ q ∙∙ r   ̇ z
  ∙∙-filler p q r k i =
    hfill (∂ i) k λ where
      j (i = i0) → p (~ j)
      j (i = i1) → r j
      j (j = i0) → q i

  -- any two definitions of double composition are equal
  ∙∙-unique : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
            → (α β : Σ[ s ꞉ w ＝ z ] Square (sym p) q r s)
            → α ＝ β
  ∙∙-unique p q r (α , α-fill) (β , β-fill) i =
    (λ k → square i k) , (λ j k → cube i j k) where
      cube : (i j : I) → p (~ j) ＝ r j
      cube i j k = hfill (∂ i ∨ ∂ k) j λ where
        j (i = i0) → α-fill j k
        j (i = i1) → β-fill j k
        j (k = i0) → p (~ j)
        j (k = i1) → r j
        j (j = i0) → q k

      square : α ＝ β
      square i k = cube i i1 k

  ∙∙-contract : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
              → (β : Σ[ s ꞉ w ＝ z ] Square (sym p) q r s)
              → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ＝ β
  ∙∙-contract p q r = ∙∙-unique p q r _

  -- For single homogenous path composition, we take `refl` as the top side:
  _∙_ : x ＝ y → y ＝ z → x ＝ z
  p ∙ q = p ∙∙ refl ∙∙ q

  ∙-filler : (p : x ＝ y) (q : y ＝ z)
           →  y  ̇    refl      ̇ y
                  ┌─    ̇   ─┐

          sym p   │    _    │   q

                  └─    ̇   ─┘
              x  ̇    p ∙ q     ̇ z
  ∙-filler p = ∙∙-filler p refl

  ∙-unique : {p : x ＝ y} {q : y ＝ z} (r : x ＝ z)
           →  y  ̇    refl      ̇ y
                  ┌─    ̇   ─┐

          sym p   │    _    │   q

                  └─    ̇   ─┘
              x  ̇      r       ̇ z
           → r ＝ p ∙ q
  ∙-unique {p} {q} r square i =
    ∙∙-unique p refl q (_ , square) (_ , (∙-filler p q)) i .fst

  ∙-filler-r : (p : x ＝ y) (q : y ＝ z)
            →  y  ̇      q       ̇ z
                   ┌─    ̇   ─┐

           sym p   │    _    │   refl

                   └─    ̇   ─┘
               x  ̇    p ∙ q     ̇ z
  ∙-filler-r {y} p q j i = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ j ∨ ~ k)
    k (i = i1) → q k
    k (j = i0) → q (i ∧ k)
    k (k = i0) → y

  ∙-filler-l : (p : x ＝ y) (q : y ＝ z)
            →  x  ̇      p       ̇ y
                   ┌─    ̇   ─┐

            refl   │    _    │   q

                   └─    ̇   ─┘
               x  ̇    p ∙ q     ̇ z
  ∙-filler-l p q j i = ∙-filler-r (sym q) (sym p) j (~ i)

  -- Double composition agrees with iterated single composition
  ∙∙＝∙ : (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
        → p ∙∙ q ∙∙ r ＝ p ∙ q ∙ r
  ∙∙＝∙ p q r j i = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → p (~ k)
      k (i = i1) → ∙-filler-r q r j k
      k (j = i0) → ∙∙-filler p q r k i
      k (j = i1) → ∙-filler p (q ∙ r) k i
      k (k = i0) → q (~ j ∧ i)


-- `ap` has good computational properties:
module _ {B : Type ℓ′} {x y : A} where
  module _ {C : Type ℓ″} {f : A → B} {g : B → C} {p : x ＝ y} where private
    ap-comp : ap (g ∘ f) p ＝ ap g (ap f p)
    ap-comp = refl

    ap-id : ap id p ＝ p
    ap-id = refl

    ap-sym : sym (ap f p) ＝ ap f (sym p)
    ap-sym = refl

    ap-refl : ap f (refl {x = x}) ＝ refl
    ap-refl = refl

  opaque
    ap-comp-∙ : (f : A → B) (p : x ＝ y) (q : y ＝ z) → ap f (p ∙ q) ＝ ap f p ∙ ap f q
    ap-comp-∙ f p q i = ∙∙-unique (ap f p) refl (ap f q)
      (ap f (p ∙ q)    , λ k j → f (∙-filler p q k j))
      (ap f p ∙ ap f q , ∙-filler _ _)
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

_＝˘⟨_⟩_ : (x : A) → y ＝ x → y ＝ z → x ＝ z
x ＝˘⟨ p ⟩ q = (sym p) ∙ q

_∎ : (x : A) → x ＝ x
_ ∎ = refl


-- Squeezing and spreading, coercions

I-eq : I → I → I
I-eq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

-- interval interpolation function
I-interp : I → I → I → I
I-interp t x y = (~ t ∧ x) ∨ (t ∧ y) ∨ (x ∧ y)

module _ {ℓ̂ : I → Level} (A : (i : I) → Type (ℓ̂ i)) where
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
  coei→i i x j = transp (λ _ → A i) (j ∨ ∂ i) x

  coe-path : (p : (i : I) → A i) (i j : I) → coe A i j (p i) ＝ p j
  coe-path p i j k = transp
    (λ l → A (I-interp k (I-interp l i j) j))
    (I-interp k (I-eq i j) i1)
    (p (I-interp k i j))


-- Transport and subst

-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transport-refl : (x : A) → transport refl x ＝ x
transport-refl x i = coe1→i _ i x

transport-filler : {A B : Type ℓ} (p : A ＝ B) (x : A)
                 → ＜ x ／ (λ i → p i) ＼ transport p x ＞
transport-filler p x i = coe0→i (λ j → p j) i x

-- We want B to be explicit in subst
subst : (B : A → Type ℓ′) (p : x ＝ y) → B x → B y
subst B p = transport (λ i → B (p i))

subst-refl : {B : A → Type ℓ} {x : A} (px : B x) → subst B refl px ＝ px
subst-refl = transport-refl


-- Function extensionality

fun-ext : {B : A → I → Type ℓ′}
          {f : Π[ a ꞉ A ] B a i0} {g : Π[ a ꞉ A ] B a i1}
        → Π[ a ꞉ A ] ＜ f a    ／                B a  ＼    g a ＞
        →            ＜ f   ／ (λ i → Π[ x ꞉ A ] B x i)  ＼ g   ＞
fun-ext p i x = p x i

fun-ext-implicit : {B : A → I → Type ℓ′}
                   {f : {a : A} → B a i0} {g : {a : A} → B a i1}
                 → ({a : A} → ＜ f {a} ／               B a ＼    g {a} ＞)
                 →            ＜ f  ／ (λ i → {x : A} → B x i) ＼ g     ＞
fun-ext-implicit p i {x} = p {x} i

fun-ext⁻ : {B : A → I → Type ℓ′}
           {f : Π[ a ꞉ A ] B a i0} {g : Π[ a ꞉ A ] B a i1}
         →            ＜ f      ／ (λ i → Π[ a ꞉ A ] B a i) ＼    g   ＞
         → Π[ x ꞉ A ] ＜ f x ／                      B x       ＼ g x ＞
fun-ext⁻ eq x i = eq i x

happly = fun-ext⁻

fun-ext-implicit⁻ : {B : A → I → Type ℓ′}
                    {f : {a : A} → B a i0} {g : {a : A} → B a i1}
                  →           ＜ f        ／ (λ i → {a : A} → B a i) ＼    g     ＞
                  → {x : A} → ＜ f {x} ／                     B x       ＼ g {x} ＞
fun-ext-implicit⁻ eq {x} i = eq i {x}

fun-ext-simple⁻ : {B : I → Type ℓ′}
                  {f : A → B i0} {g : A → B i1}
                →            ＜ f      ／ (λ i → Π[ _ ꞉ A ] B i) ＼    g   ＞
                → Π[ x ꞉ A ] ＜ f x ／ (λ i    →            B i)    ＼ g x ＞
fun-ext-simple⁻ eq x i = eq i x

happly-simple = fun-ext-simple⁻


-- h-levels

HLevel : Type₀
HLevel = ℕ

_on-paths-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

is-central : {A : Type ℓ} (c : A) → Type _
is-central {A} c = Π[ x ꞉ A ] (c ＝ x)

opaque
  is-of-hlevel : HLevel → Type ℓ → Type ℓ
  is-of-hlevel 0 A = Σ[ x ꞉ A ] is-central x
  is-of-hlevel 1 A = Π[ x ꞉ A ] is-central x
  is-of-hlevel (suc (suc h)) A = is-of-hlevel (suc h) on-paths-of A

  is-of-hlevel-β : (n : HLevel) → is-of-hlevel (suc (suc n)) A → is-of-hlevel (suc n) on-paths-of A
  is-of-hlevel-β _ = id

  is-of-hlevel-η : (n : HLevel) → is-of-hlevel (suc n) on-paths-of A → is-of-hlevel (suc (suc n)) A
  is-of-hlevel-η _ = id

is-contr : Type ℓ → Type ℓ
is-contr = is-of-hlevel 0

opaque
  unfolding is-of-hlevel
  centre : is-contr A → A
  centre = fst

  paths : (A-c : is-contr A) → is-central (centre A-c)
  paths = snd

  is-contr-β : is-contr A → Σ[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y)
  is-contr-β = id

  is-contr-η : Σ[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y) → is-contr A
  is-contr-η = id

is-prop : Type ℓ → Type ℓ
is-prop = is-of-hlevel 1

opaque
  unfolding is-of-hlevel
  is-prop-β : is-prop A → Π[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y)
  is-prop-β = id

  is-prop-η : Π[ x ꞉ A ] Π[ y ꞉ A ] (x ＝ y) → is-prop A
  is-prop-η = id

is-set : Type ℓ → Type ℓ
is-set = is-of-hlevel 2

opaque
  unfolding is-of-hlevel
  is-set-β : is-set A → Π[ x ꞉ A ] Π[ y ꞉ A ] Π[ p ꞉ (x ＝ y) ] Π[ q ꞉ x ＝ y ] (p ＝ q)
  is-set-β = id

  is-set-η : Π[ x ꞉ A ] Π[ y ꞉ A ] Π[ p ꞉ (x ＝ y) ] Π[ q ꞉ x ＝ y ] (p ＝ q) → is-set A
  is-set-η = id


-- Singleton contractibility

fibre : {A : Type ℓ} {B : Type ℓ′} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ′)
fibre {A} f y = Σ[ x ꞉ A ] (f x ＝ y)

SingletonP : (A : I → Type ℓ) (a : A i0) → Type _
SingletonP A a = Σ[ x ꞉ A i1 ] ＜ a ／ A ＼ x ＞

Singleton : {A : Type ℓ} → A → Type _
Singleton {A} = SingletonP (λ _ → A)

singleton-is-prop : {A : Type ℓ} {a : A} (s : Singleton a)
                  → (a , refl) ＝ s
singleton-is-prop (_ , path) i = path i , square i where
    square : Square refl refl path path
    square i j = path (i ∧ j)

opaque
  unfolding is-of-hlevel
  singleton-is-contr : {A : Type ℓ} {a : A} (s : Singleton a)
                     → is-contr (Singleton a)
  singleton-is-contr {a} _ = (a , refl) , singleton-is-prop

  singletonP-is-contr : (A : I → Type ℓ) (a : A i0) → is-contr (SingletonP A a)
  singletonP-is-contr A a .fst = _ , transport-filler (λ i → A i) a
  singletonP-is-contr A a .snd (x , p) i = _ , λ j → fill A (∂ i) j λ where
    k (i = i0) → transport-filler (λ i → A i) a k
    k (i = i1) → p k
    k (k = i0) → a

inspect : (x : A) → Singleton x
inspect x = x , refl


-- Path induction (J) and its computation rule

module _ (P : (y : A) → x ＝ y → Type ℓ′) (d : P x refl) where opaque
  unfolding is-of-hlevel singleton-is-contr

  J : (p : x ＝ y) → P y p
  J {y} p = transport (λ i → P (path i .fst) (path i .snd)) d where
    path : Path (Σ A λ t → x ＝ t) (x , refl) (y , p)
    path = singleton-is-contr (y , p) .snd _

  J-refl : J refl ＝ d
  J-refl = transport-refl d

  J-∙ : (p : x ＝ y) (q : y ＝ z)
      → J (p ∙ q) ＝ transport (λ i → P (q i) (λ j → ∙-filler-l p q i j)) (J p)
  J-∙ p q k =
    transp
      (λ i → P (q (i ∨ ~ k))
      (λ j → ∙-filler-l p q (i ∨ ~ k) j)) (~ k)
      (J (λ j → ∙-filler-l p q (~ k) j))

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

  J² : {y : A} (p : x ＝ y) {z : P y p} (q : d y p ＝ z) → Q _ p _ q
  J² p = J ΠQ (λ _ → J (Q x refl) r) p _

  J²-refl : J² refl refl ＝ r
  J²-refl = (λ i → J-refl ΠQ (λ _ → J (Q x refl) r) i _ refl) ∙ J-refl (Q x refl) _

-- A prefix operator version of J that is more suitable to be nested

module _ {P : ∀ y → x ＝ y → Type ℓ′} (d : P x refl) where

  J>_ : ∀ y → (p : x ＝ y) → P y p
  J>_ _ p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  infix 10 J>_


-- Converting to and from a PathP

pathP＝path : (P : I → Type ℓ) (p : P i0) (q : P i1)
            →  ＜ p ／ P ＼ q ＞
            ＝ (transport (λ i → P i) p ＝ q)
pathP＝path P p q i =
  ＜ transport-filler (λ j → P j) p i ／ (λ j → P (i ∨ j)) ＼ q ＞

pathP＝path⁻ : (P : I → Type ℓ) (p : P i0) (q : P i1)
             →  ＜ p ／ P ＼  q ＞
             ＝ (p ＝ transport (λ i → P (~ i)) q)
pathP＝path⁻ P p q i =
  ＜ p ／ (λ j → P (~ i ∧ j)) ＼ transport-filler (λ j → P (~ j)) q i ＞



module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where opaque
  -- to-pathP : (transport (λ i → A i) x ＝ y) → ＜ x ／ A ＼ y ＞
  to-pathP : (coe0→1 A x ＝ y) → ＜ x ／ A ＼ y ＞
  to-pathP p i = hcomp (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe0→i A i x

  -- from-pathP : ＜ x ／ A ＼ y ＞ → transport (λ i → A i) x ＝ y
  from-pathP : ＜ x ／ A ＼ y ＞ → coe0→1 A x ＝ y
  from-pathP p i = coei→1 A i (p i)

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where opaque
  unfolding to-pathP
  to-pathP⁻ : x ＝ coe1→0 A y → ＜ x ／ A ＼ y ＞
  to-pathP⁻ p = symP $ to-pathP {A = λ j → A (~ j)} (λ i → p (~ i))

  from-pathP⁻ : ＜ x ／ A ＼ y ＞ → x ＝ coe1→0 A y
  from-pathP⁻ p = sym $ from-pathP (λ i → p (~ i))

  to-from-pathP : (p : ＜ x ／ A ＼ y ＞) → to-pathP (from-pathP p) ＝ p
  to-from-pathP p i j = hcomp (i ∨ ∂ j) λ where
    k (i = i1) → transp (λ l → A (j ∧ (k ∨ l))) (~ j ∨ k) (p (j ∧ k)) -- TODO use `coe` ?
    k (j = i0) → x
    k (j = i1) → coei→1 A k (p k)
    k (k = i0) → coe0→i A j x

  -- just pray
  from-to-pathP : (p : coe0→1 A x ＝ y) → from-pathP {A = A} (to-pathP p) ＝ p
  from-to-pathP p i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → coei→1 A (j ∨ ~ i) $
        transp (λ l → A (j ∨ (~ i ∧ l))) (i ∨ j) $ coe0→i A j x -- TODO use `coe` ?

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
Σ-pathP : {x y : Σ A B}
          (p :              x .fst ＝ y .fst                 )
        →   ＜ x .snd ／     (λ i → B (p i))    ＼ y .snd ＞
        →      x                   ＝              y
Σ-pathP p q i = p i , q i

Σ-path : {x y : Σ A B}
         (p : x .fst ＝ y .fst)
       → subst B p (x .snd) ＝ (y .snd)
       → x ＝ y
Σ-path p q = Σ-pathP p (to-pathP q)


-- Path transport

opaque
  unfolding _∙∙_∙∙_
  transport-path : {x y x′ y′ : A}
                 → (p : x ＝ y)
                 → (left : x ＝ x′) (right : y ＝ y′)
                 → transport (λ i → left i ＝ right i) p ＝ sym left ∙ p ∙ right
  transport-path {A} p left right = lemma ∙ ∙∙＝∙ _ _ _
    where
    lemma : transport (λ i → left i ＝ right i) p ＝ sym left ∙∙ p ∙∙ right
    lemma i j = hcomp (~ i ∨ ∂ j) λ where
      k (k = i0) → coei→1 (λ _ → A) i (p j)
      k (i = i0) → hfill (∂ j) k λ where
        k (k = i0) → coe0→1 (λ _ → A) (p j)
        k (j = i0) → coei→1 (λ _ → A) k (left k)
        k (j = i1) → coei→1 (λ _ → A) k (right k)
      k (j = i0) → coei→1 (λ _ → A) (k ∨ i) (left k)
      k (j = i1) → coei→1 (λ _ → A) (k ∨ i) (right k)

subst-path-left : {x y x′ : A}
                → (p : x ＝ y)
                → (left : x ＝ x′)
                → subst (λ e → e ＝ y) left p ＝ sym left ∙ p
subst-path-left {y} p left =
  subst (λ e → e ＝ y) left p     ＝⟨⟩
  transport (λ i → left i ＝ y) p ＝⟨ transport-path p left refl ⟩
  sym left ∙ p ∙ refl             ＝⟨ ap (sym left ∙_) (sym (∙-filler-l _ _)) ⟩
  sym left ∙ p                    ∎

subst-path-right : {x y y′ : A}
                 → (p : x ＝ y)
                 → (right : y ＝ y′)
                 → subst (λ e → x ＝ e) right p ＝ p ∙ right
subst-path-right {x} p right =
  subst (λ e → x ＝ e) right p     ＝⟨⟩
  transport (λ i → x ＝ right i) p ＝⟨ transport-path p refl right ⟩
  sym refl ∙ p ∙ right             ＝⟨⟩
  refl ∙ p ∙ right                 ＝⟨ sym (∙-filler-r _ _) ⟩
  p ∙ right                        ∎

subst-path-both : {x x′ : A}
                → (p : x ＝ x)
                → (adj : x ＝ x′)
                → subst (λ x → x ＝ x) adj p ＝ sym adj ∙ p ∙ adj
subst-path-both p adj = transport-path p adj adj


-- TODO move somewhere?
it : ⦃ A ⦄ → A
it ⦃ (a) ⦄ = a

_weakly-stable_ : (S : Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S weakly-stable A = S A → A

-- Explicit type hint
the : (A : Type ℓ) → A → A
the _ a = a
