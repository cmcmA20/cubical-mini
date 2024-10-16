{-# OPTIONS --safe #-}
module Foundations.Base where

open import Foundations.Prim.Type       public
open import Foundations.Prim.Interval   public
open import Foundations.Prim.Extension  public
open import Foundations.Prim.Kan        public
open import Foundations.Prim.Glue       public

open import Foundations.Notation   public
open import Foundations.Pi.Base    public
open import Foundations.Sigma.Base public

open import Agda.Builtin.Nat
  using (zero; suc)
  renaming (Nat to ℕ)
open import Agda.Builtin.Unit
  renaming (⊤ to ⊤ₜ)
  public

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓᵃ ℓᵇ ℓᶜ : Level
  A : Type ℓ
  B : A → Type ℓ′
  x y z w : A

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

Square : {a₀₀ a₀₁ : A} (p : a₀₀ ＝ a₀₁)
         {a₁₀ : A} (q : a₀₀ ＝ a₁₀)
         {a₁₁ : A} (r : a₁₀ ＝ a₁₁) (s : a₀₁ ＝ a₁₁)
       → Type (level-of-type A)
Square p q r s = ＜ q ／ (λ j → p j ＝ r j) ＼ s ＞

infix 0 Square-syntax
Square-syntax : (d : ⊤ₜ)
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

apˢ : {B : Type ℓ′} (f : A → B)
      (p : x ＝ y) → f x ＝ f y
apˢ f p i = f (p i)
{-# INLINE apˢ #-}


apᴾ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
      (f : (i : I) → Π[ a ꞉ A i ] B i a) {x : A i0} {y : A i1}
      (p : ＜      x    ／ (λ i →       A i) ＼         y ＞)
    →      ＜ f i0 x ／ (λ i    →  B i (p i))   ＼ f i1 y ＞
apᴾ f p i = f i (p i)
{-# INLINE apᴾ #-}

ap² : {ℓ ℓ′ ℓ″ : Level}
      {A : Type ℓ} {B : A → Type ℓ′} {C : Π[ a ꞉ A ] Π[ b ꞉ B a ] Type ℓ″}
      (f : Π[ a ꞉ A ] Π[ b ꞉ B a ] C a b)
      {x y : A} (p : x ＝ y) {u : B x} {v : B y}
      (q : ＜     u    ／ (λ i →          B (p i)) ＼        v ＞)
    →      ＜ f x u ／ (λ i    → C (p i) (q    i ))   ＼ f y v ＞
ap² f p q i = f (p i) (q i)
{-# INLINE ap² #-}

apᴾ² : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ′}
       {C : (i : I) → Π[ a ꞉ A i ] (B i a → Type ℓ″)}
       (f : (i : I) → Π[ a ꞉ A i ] Π[ b ꞉ B i a ] C i a b)
       {x : A i0} {y : A i1} {u : B i0 x} {v : B i1 y}
       (p : ＜      x         ／ (λ i →      A i)          ＼            y   ＞)
       (q : ＜        u    ／ (λ i    →            B i (p i)) ＼           v ＞)
     →      ＜ f i0 x u ／ (λ i       → C i (p i) (q      i ))   ＼ f i1 y v ＞
apᴾ² f p q i = f i (p i) (q i)
{-# INLINE apᴾ² #-}


opaque
  infix 6 _∙∙_∙∙_
   -- Double whiskering
  _∙∙_∙∙_ : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ a₁′ : A i1}
          →    a₀ ＝ a₀′ → ＜ a₀′ ／ A ＼ a₁ ＞ → a₁ ＝ a₁′
          → ＜ a₀              ／    A    ＼            a₁′ ＞
  (p ∙∙ q ∙∙ r) i = hcomp (∂ i) λ where
    j (i = i0) → p (~ j)
    j (i = i1) → r j
    j (j = i0) → q i

  ∙∙-filler
    : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ a₁′ : A i1}
    → (p : a₀ ＝ a₀′) (q : ＜ a₀′ ／ A ＼ a₁ ＞) (r : a₁ ＝ a₁′)
    → ＜ q ／ (λ i → ＜ p (~ i) ／ A ＼ r i ＞) ＼ p ∙∙ q ∙∙ r ＞
  ∙∙-filler p q r k i =
    hfill (∂ i) k λ where
      j (i = i0) → p (~ j)
      j (i = i1) → r j
      j (j = i0) → q i

  -- any two definitions of double composition are equal
  ∙∙-unique : {A : Type ℓᵃ} {x y z w : A}
              (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
            → (α β : Σ[ s ꞉ w ＝ z ] Square (symₚ p) q r s)
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

  ∙∙-contract : {A : Type ℓᵃ} {x y z w : A}
                (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
              → (β : Σ[ s ꞉ w ＝ z ] Square (symₚ p) q r s)
              → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ＝ β
  ∙∙-contract p q r = ∙∙-unique p q r _

  -- For single homogenous path composition, we take `refl` as the top side:
  infixr 30 _∙ₚ_
  _∙ₚ_ : x ＝ y → y ＝ z → x ＝ z
  p ∙ₚ q = p ∙∙ reflₚ ∙∙ q

  ∙-filler : (p : x ＝ y) (q : y ＝ z)
           →  y  ̇    reflₚ     ̇ y
                  ┌─    ̇   ─┐

         symₚ p   │    _    │   q

                  └─    ̇   ─┘
              x  ̇    p ∙ₚ q    ̇ z
  ∙-filler p = ∙∙-filler p reflₚ

  ∙-unique : {p : x ＝ y} {q : y ＝ z} (r : x ＝ z)
           →  y  ̇    reflₚ     ̇ y
                  ┌─    ̇   ─┐

         symₚ p   │    _    │   q

                  └─    ̇   ─┘
              x  ̇      r       ̇ z
           → r ＝ p ∙ₚ q
  ∙-unique {p} {q} r square i =
    ∙∙-unique p reflₚ q (_ , square) (_ , ∙-filler p q) i .fst

  ∙-filler-r : (p : x ＝ y) (q : y ＝ z)
            →  y  ̇      q       ̇ z
                   ┌─    ̇   ─┐

          symₚ p   │    _    │   reflₚ

                   └─    ̇   ─┘
               x  ̇    p ∙ₚ q    ̇ z
  ∙-filler-r {y} p q j i = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ j ∨ ~ k)
    k (i = i1) → q k
    k (j = i0) → q (i ∧ k)
    k (k = i0) → y

  ∙-filler-l : (p : x ＝ y) (q : y ＝ z)
            →  x  ̇      p       ̇ y
                   ┌─    ̇   ─┐

           reflₚ   │    _    │   q

                   └─    ̇   ─┘
               x  ̇    p ∙ₚ q    ̇ z
  ∙-filler-l p q j i = ∙-filler-r (symₚ q) (symₚ p) j (~ i)

  -- Double composition agrees with iterated single composition
  ∙∙=∙ : (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
       → p ∙∙ q ∙∙ r ＝ p ∙ₚ q ∙ₚ r
  ∙∙=∙ p q r j i = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → p (~ k)
      k (i = i1) → ∙-filler-r q r j k
      k (j = i0) → ∙∙-filler p q r k i
      k (j = i1) → ∙-filler p (q ∙ₚ r) k i
      k (k = i0) → q (~ j ∧ i)

instance
  Refl-Pathᴾ : Refl λ x y → ＜ x ／ (λ _ → A) ＼ y ＞
  Refl-Pathᴾ .refl {x} _ = x

  Dual-Pathᴾ
    : {A : I → Type ℓ}
    → Dual (λ x y → ＜ x ／ A ＼ y ＞) (λ x y → ＜ x ／ (λ i → A (~ i)) ＼ y ＞)
  Dual-Pathᴾ ._ᵒᵖ p i = p (~ i)

  GInvol-Pathᴾ
    : {A : I → Type ℓ}
    → GInvol (λ x y → ＜ x ／ A ＼ y ＞) (λ x y → ＜ x ／ (λ i → A (~ i)) ＼ y ＞)
  GInvol-Pathᴾ .invol p _ = p

  Trans-Path : Trans (Path A)
  Trans-Path ._∙_ = _∙ₚ_


-- `ap` has good computational properties:
module _ {A : Type ℓ} {B : Type ℓ′} {x y : A} where
  module _ {C : Type ℓ″} {f : A → B} {g : B → C} {p : x ＝ y} where private
    ap-comp : ap (g ∘ f) p ＝ ap g (ap f p)
    ap-comp = refl

    ap-id : ap id p ＝ p
    ap-id = refl

    ap-sym : ap f p ⁻¹ ＝ ap f (p ⁻¹)
    ap-sym = refl

    ap-refl : ap f (refl {x = x}) ＝ refl
    ap-refl = refl

  opaque
    ap-comp-∙ : (f : A → B) (p : x ＝ y) (q : y ＝ z) → ap f (p ∙ q) ＝ ap f p ∙ ap f q
    ap-comp-∙ f p q i = ∙∙-unique (ap f p) refl (ap f q)
      (ap f (p ∙ q)    , λ k j → f (∙-filler p q k j))
      (ap f p ∙ ap f q , ∙-filler _ _)
      i .fst


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
transport-refl : {A : Type ℓ} (x : A) → transport refl x ＝ x
transport-refl x i = coe1→i _ i x

transport-filler : {A B : Type ℓ} (p : A ＝ B) (x : A)
                 → ＜ x ／ (λ i → p i) ＼ transport p x ＞
transport-filler p x i = coe0→i (λ j → p j) i x

-- We want B to be explicit in subst
subst : (B : A → Type ℓ′) (p : x ＝ y) → B x → B y
subst B p = transport (λ i → B (p i))

subst-refl : {A : Type ℓ} {B : A → Type ℓ′} {x : A} (px : B x) → subst B refl px ＝ px
subst-refl = transport-refl


-- Function extensionality

fun-ext : {A : Type ℓ} {B : A → I → Type ℓ′}
          {f : Π[ a ꞉ A ] B a i0} {g : Π[ a ꞉ A ] B a i1}
        → Π[ a ꞉ A ] ＜ f a    ／                B a  ＼    g a ＞
        →            ＜ f   ／ (λ i → Π[ x ꞉ A ] B x i)  ＼ g   ＞
fun-ext p i x = p x i

happly : {A : Type ℓ} {B : A → I → Type ℓ′}
         {f : Π[ a ꞉ A ] B a i0} {g : Π[ a ꞉ A ] B a i1}
       →            ＜ f      ／ (λ i → Π[ a ꞉ A ] B a i) ＼    g   ＞
       → Π[ x ꞉ A ] ＜ f x ／                      B x       ＼ g x ＞
happly eq x i = eq i x


-- Syntax for chains of equational reasoning

infix  3 _∎
_∎
  : {A : Type ℓᵃ}
    {_~_ : A → A → 𝒰 ℓ} ⦃ rfl : Refl _~_ ⦄
  → (x : A) → x ~ x
_ ∎ = refl
{-# INLINE _∎ #-}

infixr 2 _~⟨⟩_ _=⟨⟩_
_~⟨⟩_
  : {A : Type ℓᵃ} {B : Type ℓᵇ}
    {_~I_ : A → B → 𝒰 ℓ} {_~O_ : B → A → 𝒰 ℓ}
    ⦃ sy : Dual _~I_ _~O_ ⦄ -- for inference TODO improve
  → (x : B) {y : A} → x ~O y → x ~O y
_~⟨⟩_ _ xy = xy
{-# INLINE _~⟨⟩_ #-}

_=⟨⟩_ : {A : Type ℓᵃ} → (x : A) {y : A} → x ＝ y → x ＝ y
_=⟨⟩_ = _~⟨⟩_

=→~⁻
  : {A : Type ℓᵃ}
    {_~_ : A → A → 𝒰 ℓ}
    ⦃ rfl : Refl _~_ ⦄
    {x y : A} → x ＝ y → y ~ x
=→~⁻ {_~_} {x} p = subst (_~ x) p refl
{-# INLINE =→~⁻ #-}

=→~
  : {A : Type ℓᵃ}
    {_~_ : A → A → 𝒰 ℓ}
    ⦃ rfl : Refl _~_ ⦄
    {x y : A} → x ＝ y → x ~ y
=→~ p = =→~⁻ (p ⁻¹)
{-# INLINE =→~ #-}

infixr 2 _~⟨_⟩_ _=⟨_⟩_
_~⟨_⟩_
  : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
    {_~L_ : A → B → 𝒰 ℓ} {_~R_ : B → C → 𝒰 ℓ′} {_~O_ : A → C → 𝒰 ℓ″}
    ⦃ tra : Comp _~L_ _~R_ _~O_ ⦄
  → (x : A) {y : B} {z : C} → x ~L y → y ~R z → x ~O z
_ ~⟨ x~y ⟩ y~z = x~y ∙ y~z
{-# INLINE _~⟨_⟩_ #-}

_=⟨_⟩_
  : {A : Type ℓᵃ} {B : Type ℓᵇ}
    {_~L_ : A → A → 𝒰 ℓ} {_~R_ : A → B → 𝒰 ℓ′} {_~O_ : A → B → 𝒰 ℓ′}
    ⦃ rfl : Refl _~L_ ⦄
    ⦃ tra : Comp _~L_ _~R_ _~O_ ⦄
  → (x : A) {y : A} {z : B} → x ＝ y → y ~R z → x ~O z
_=⟨_⟩_ {_~L_} x {y} x=y = x ~⟨ =→~ x=y ⟩_
{-# INLINE _=⟨_⟩_ #-}

infixr 2 _~⟨_⟨_ _=⟨_⟨_
_~⟨_⟨_
  : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
    {_~L_ : A → B → 𝒰 ℓ} {_~L′_ : B → A → 𝒰 ℓ} {_~R_ : B → C → 𝒰 ℓ′} {_~O_ : A → C → 𝒰 ℓ″}
    ⦃ tra : Comp _~L_ _~R_ _~O_ ⦄ ⦃ sy : Dual _~L′_ _~L_ ⦄
  → (x : A) {y : B} {z : C} → y ~L′ x → y ~R z → x ~O z
x ~⟨ p ⟨ q = p ⁻¹ ∙ q
{-# INLINE _~⟨_⟨_ #-}

_=⟨_⟨_
  : {A : Type ℓᵃ} {B : Type ℓᵇ}
    {_~L_ : A → A → 𝒰 ℓ} {_~R_ : A → B → 𝒰 ℓ′} {_~O_ : A → B → 𝒰 ℓ′}
    ⦃ rfl : Refl _~L_ ⦄
    ⦃ tra : Comp _~L_ _~R_ _~O_ ⦄
  → (x : A) {y : A} {z : B} → y ＝ x → y ~R z → x ~O z
_=⟨_⟨_ {_~L_} x {y} y=x = x ~⟨ =→~⁻ y=x ⟩_
{-# INLINE _=⟨_⟨_ #-}

infixr 2 ~⟨⟩-syntax =⟨⟩-syntax
~⟨⟩-syntax
  : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
    {_~L_ : A → B → 𝒰 ℓ} {_~R_ : B → C → 𝒰 ℓ′} {_~O_ : A → C → 𝒰 ℓ″}
    ⦃ tra : Comp _~L_ _~R_ _~O_ ⦄
  → (x : A) {y : B} {z : C} → x ~L y → y ~R z → x ~O z
~⟨⟩-syntax = _~⟨_⟩_
syntax ~⟨⟩-syntax x (λ i → B) y = x ~[ i ]⟨ B ⟩ y
{-# INLINE ~⟨⟩-syntax #-}

=⟨⟩-syntax : {A : Type ℓᵃ} (x : A) {y z : A} → x ＝ y → y ＝ z → x ＝ z
=⟨⟩-syntax = _=⟨_⟩_
syntax =⟨⟩-syntax x (λ i → B) y = x =[ i ]⟨ B ⟩ y
{-# INLINE =⟨⟩-syntax #-}

infixr 3 =⟨⟩⟨⟩-syntax
=⟨⟩⟨⟩-syntax : (x y : A) → x ＝ y → y ＝ z → z ＝ w → x ＝ w
=⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
syntax =⟨⟩⟨⟩-syntax x y B C = x =⟨ B ⟩= y =⟨ C ⟩=
{-# INLINE =⟨⟩⟨⟩-syntax #-}

infixr 2.5 _=⟨_⟩=⟨_⟩_
_=⟨_⟩=⟨_⟩_ : (x : A) → x ＝ y → y ＝ z → z ＝ w → x ＝ w
_ =⟨ x=y ⟩=⟨ y=z ⟩ z=w = x=y ∙∙ y=z ∙∙ z=w
{-# INLINE _=⟨_⟩=⟨_⟩_ #-}


-- h-levels

HLevel : Type₀
HLevel = ℕ

_on-paths-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = (a a′ : A) → S (a ＝ a′)

is-central : {A : Type ℓ} (c : A) → Type _
is-central {A} c = (x : A) → c ＝ x

is-of-hlevel : HLevel → Type ℓ → Type ℓ
is-of-hlevel 0 A = Σ A λ x → is-central x
is-of-hlevel 1 A = (x : A) → is-central x
is-of-hlevel (suc (suc h)) A = is-of-hlevel (suc h) on-paths-of A

is-contr : Type ℓ → Type ℓ
is-contr = is-of-hlevel 0

-- TODO remove this?
centre : is-contr A → A
centre = fst

-- TODO remove this?
paths : (A-c : is-contr A) → is-central (centre A-c)
paths = snd

is-prop : Type ℓ → Type ℓ
is-prop = is-of-hlevel 1

is-set : Type ℓ → Type ℓ
is-set = is-of-hlevel 2

is-of-hlevelᴱ : HLevel → Type ℓ → Type ℓ
is-of-hlevelᴱ 0       A = is-contrᴱ A
is-of-hlevelᴱ (suc h) A = is-of-hlevelᴱ h on-paths-of A

is-propᴱ : Type ℓ → Type ℓ
is-propᴱ = is-of-hlevelᴱ 1


-- Singleton contractibility

fibre : {A : Type ℓ} {B : Type ℓ′} (f : A → B) (y : B) → Type (ℓ ⊔ ℓ′)
fibre {A} f y = Σ[ x ꞉ A ] (f x ＝ y)

Singletonᴾ : (A : I → Type ℓ) (a : A i0) → Type _
Singletonᴾ A a = Σ[ x ꞉ A i1 ] ＜ a ／ A ＼ x ＞

Singletonₚ : {A : Type ℓ} → A → Type _
Singletonₚ {A} = Singletonᴾ (λ _ → A)

opaque
  singletonₚ-is-prop : {A : Type ℓ} {a : A} (s : Singletonₚ a)
                     → (a , reflₚ) ＝ s
  singletonₚ-is-prop (_ , path) i = path i , square i where
      square : Square refl refl path path
      square i j = path (i ∧ j)

  singletonᴾ-is-prop
    : (A : I → Type ℓ) (a : A i0) (s : Singletonᴾ A a)
    → (transport (λ i → A i) a , transport-filler (λ i → A i) a) ＝ s
  singletonᴾ-is-prop A a (x , p) i = _ , λ j → fill A (∂ i) j λ where
    k (i = i0) → transport-filler (λ i → A i) a k
    k (i = i1) → p k
    k (k = i0) → a

singletonₚ-is-contr : {A : Type ℓ} {a : A} (s : Singletonₚ a)
                    → is-contr (Singletonₚ a)
singletonₚ-is-contr {a} _ = (a , refl) , singletonₚ-is-prop

singletonᴾ-is-contr : (A : I → Type ℓ) (a : A i0) → is-contr (Singletonᴾ A a)
singletonᴾ-is-contr A a .fst = _
singletonᴾ-is-contr A a .snd = singletonᴾ-is-prop A a


-- Path induction (J) and its computation rule

module _ {A : Type ℓ} {x : A} (P : (y : A) → x ＝ y → Type ℓ′) (d : P x refl) where
  Jₚ : (p : x ＝ y) → P y p
  Jₚ {y} p = transport (λ i → P (path i .fst) (path i .snd)) d where
    path : Path (Σ[ t ꞉ A ] (x ＝ t)) (x , refl) (y , p)
    path = singletonₚ-is-contr (y , p) .snd _

  opaque
    unfolding singletonₚ-is-prop
    Jₚ-refl : Jₚ refl ＝ d
    Jₚ-refl = transport-refl d

  opaque
    Jₚ-∙ : (p : x ＝ y) (q : y ＝ z)
         → Jₚ (p ∙ q) ＝ transport (λ i → P (q i) (λ j → ∙-filler-l p q i j)) (Jₚ p)
    Jₚ-∙ p q k =
      transp
        (λ i → P (q (i ∨ ~ k))
        (λ j → ∙-filler-l p q (i ∨ ~ k) j)) (~ k)
        (Jₚ (λ j → ∙-filler-l p q (~ k) j))

-- Multi-variable versions of J
module _ {A : Type ℓ} {B : A → Type ℓ′} {x : A} {b : B x}
  (P : (y : A) (p : x ＝ y) (z : B y) (q : ＜ b ／ (λ i → B (p i)) ＼ z ＞) → Type ℓ″)
  (d : P _ refl _ refl) where

  Jₚᵈ : {y : A} (p : x ＝ y) {z : B y} (q : ＜ b ／ (λ i → B (p i)) ＼ z ＞) → P _ p _ q
  Jₚᵈ _ q = transport (λ i → P _ _ _ (λ j → q (i ∧ j))) d

  Jₚᵈ-refl : Jₚᵈ refl refl ＝ d
  Jₚᵈ-refl = transport-refl d

module _ {A : Type ℓ} {x : A}
  {P : (y : A) → x ＝ y → Type ℓ′} {d : (y : A) (p : x ＝ y) → P y p}
  (Q : (y : A) (p : x ＝ y) (z : P y p) → d y p ＝ z → Type ℓ″)
  (r : Q _ refl _ refl) where

  private
    ΠQ : (y : A) → x ＝ y → _
    ΠQ y p = ∀ z q → Q y p z q

  Jₚ² : {y : A} (p : x ＝ y) {z : P y p} (q : d y p ＝ z) → Q _ p _ q
  Jₚ² p = Jₚ ΠQ (λ _ → Jₚ (Q x refl) r) p _

  Jₚ²-refl : Jₚ² reflₚ reflₚ ＝ r
  Jₚ²-refl = (λ i → Jₚ-refl ΠQ (λ _ → Jₚ (Q x refl) r) i _ refl) ∙ₚ Jₚ-refl (Q x refl) _

-- A prefix operator version of J that is more suitable to be nested

module _ {P : ∀ y → x ＝ y → Type ℓ′} (d : P x reflₚ) where

  Jₚ>_ : ∀ y → (p : x ＝ y) → P y p
  Jₚ>_ _ p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  infix 10 Jₚ>_


-- Converting to and from a Pathᴾ

pathᴾ=path : (P : I → Type ℓ) (p : P i0) (q : P i1)
           →  ＜ p ／ P ＼ q ＞
           ＝ (transport (λ i → P i) p ＝ q)
pathᴾ=path P p q i =
  ＜ transport-filler (λ j → P j) p i ／ (λ j → P (i ∨ j)) ＼ q ＞

pathᴾ=path⁻ : (P : I → Type ℓ) (p : P i0) (q : P i1)
            →  ＜ p ／ P ＼  q ＞
            ＝ (p ＝ transport (λ i → P (~ i)) q)
pathᴾ=path⁻ P p q i =
  ＜ p ／ (λ j → P (~ i ∧ j)) ＼ transport-filler (λ j → P (~ j)) q i ＞



module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where opaque
  -- to-pathᴾ : (transport (λ i → A i) x ＝ y) → ＜ x ／ A ＼ y ＞
  to-pathᴾ : (coe0→1 A x ＝ y) → ＜ x ／ A ＼ y ＞
  to-pathᴾ p i = hcomp (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe0→i A i x

  -- from-pathᴾ : ＜ x ／ A ＼ y ＞ → transport (λ i → A i) x ＝ y
  from-pathᴾ : ＜ x ／ A ＼ y ＞ → coe0→1 A x ＝ y
  from-pathᴾ p i = coei→1 A i (p i)

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where opaque
  unfolding to-pathᴾ
  to-pathᴾ⁻ : x ＝ coe1→0 A y → ＜ x ／ A ＼ y ＞
  to-pathᴾ⁻ p = to-pathᴾ {A = λ j → A (~ j)} (λ i → p (~ i)) ⁻¹

  from-pathᴾ⁻ : ＜ x ／ A ＼ y ＞ → x ＝ coe1→0 A y
  from-pathᴾ⁻ p = from-pathᴾ (λ i → p (~ i)) ⁻¹

  to-from-pathᴾ : (p : ＜ x ／ A ＼ y ＞) → to-pathᴾ (from-pathᴾ p) ＝ p
  to-from-pathᴾ p i j = hcomp (i ∨ ∂ j) λ where
    k (i = i1) → transp (λ l → A (j ∧ (k ∨ l))) (~ j ∨ k) (p (j ∧ k)) -- TODO use `coe` ?
    k (j = i0) → x
    k (j = i1) → coei→1 A k (p k)
    k (k = i0) → coe0→i A j x

  -- just pray
  from-to-pathᴾ : (p : coe0→1 A x ＝ y) → from-pathᴾ {A = A} (to-pathᴾ p) ＝ p
  from-to-pathᴾ p i j =
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
Σ-pathᴾ
  : {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ′}
  → {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  → (p : ＜ x .fst ／ A ＼ y .fst ＞)
  → ＜ x .snd ／ (λ i → B i (p i)) ＼ y .snd ＞
  → ＜ x ／ (λ i → Σ (A i) (B i)) ＼ y ＞
Σ-pathᴾ p q i = p i , q i

_,ₚ_ = Σ-pathᴾ
infixr 4 _,ₚ_

Σ-path : {x y : Σ A B}
         (p : x .fst ＝ y .fst)
       → subst B p (x .snd) ＝ (y .snd)
       → x ＝ y
Σ-path p q = p ,ₚ to-pathᴾ q


-- Path transport

opaque
  unfolding _∙∙_∙∙_
  transport-path : {A : Type ℓᵃ} {x y x′ y′ : A}
                 → (p : x ＝ y)
                 → (left : x ＝ x′) (right : y ＝ y′)
                 → transport (λ i → left i ＝ right i) p ＝ left ⁻¹ ∙ p ∙ right
  transport-path {A} p left right = lemma ∙ ∙∙=∙ _ _ _
    where
    lemma : transport (λ i → left i ＝ right i) p ＝ symₚ left ∙∙ p ∙∙ right
    lemma i j = hcomp (~ i ∨ ∂ j) λ where
      k (k = i0) → coei→1 (λ _ → A) i (p j)
      k (i = i0) → hfill (∂ j) k λ where
        k (k = i0) → coe0→1 (λ _ → A) (p j)
        k (j = i0) → coei→1 (λ _ → A) k (left k)
        k (j = i1) → coei→1 (λ _ → A) k (right k)
      k (j = i0) → coei→1 (λ _ → A) (k ∨ i) (left k)
      k (j = i1) → coei→1 (λ _ → A) (k ∨ i) (right k)

opaque
  subst-path-left : {A : Type ℓᵃ} {x y x′ : A}
                  → (p : x ＝ y)
                  → (left : x ＝ x′)
                  → subst (λ e → e ＝ y) left p ＝ left ⁻¹ ∙ p
  subst-path-left {y} p left =
    subst (λ e → e ＝ y) left p      ~⟨⟩
    transport (λ i → left i ＝ y) p  ~⟨ transport-path p left refl ⟩
    left ⁻¹ ∙ p ∙ reflₚ              ~⟨ ap (sym left ∙ₚ_) (∙-filler-l _ _) ⟨
    left ⁻¹ ∙ p                      ∎

  subst-path-right : {A : Type ℓᵃ} {x y y′ : A}
                   → (p : x ＝ y)
                   → (right : y ＝ y′)
                   → subst (λ e → x ＝ e) right p ＝ p ∙ right
  subst-path-right {x} p right =
    subst (λ e → x ＝ e) right p      ~⟨⟩
    transport (λ i → x ＝ right i) p  ~⟨ transport-path p refl right ⟩
    refl ⁻¹ ∙ p ∙ right               ~⟨⟩
    refl ∙ p ∙ right                  ~⟨ ∙-filler-r _ _ ⟨
    p ∙ right                         ∎

  subst-path-both : {x x′ : A}
                  → (p : x ＝ x)
                  → (adj : x ＝ x′)
                  → subst (λ x → x ＝ x) adj p ＝ symₚ adj ∙ₚ p ∙ₚ adj
  subst-path-both p adj = transport-path p adj adj


-- TODO move this section somewhere?

auto : {ℓ : Level} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a

-- Explicit type hint
the : (A : Type ℓ) → A → A
the _ a = a

inspect : (x : A) → Singletonₚ x
inspect x = x , refl

record Recall {A : Type ℓ} {B : A → Type ℓ′}
  (f : Π[ x ꞉ A ] B x) (x : A) (y : B x) : Type (ℓ ⊔ ℓ′) where
  constructor ⟪_⟫
  field eq : f x ＝ y

recall : {A : Type ℓ} {B : A → Type ℓ′}
         (f : Π[ x ꞉ A ] B x) (x : A)
       → Recall f x (f x)
recall f x = ⟪ refl ⟫

infix 30 _∈!_
_∈!_ : {A : Type ℓ} {ℙA : Type ℓ′} ⦃ m : Membership A ℙA ℓ″ ⦄
     → A → ℙA → Type ℓ″
x ∈! y = is-contr (x ∈ y)

instance
  refl-helper : {A : Type ℓ} {x : A} → x ＝ x
  refl-helper {x} i = x
  {-# INCOHERENT refl-helper #-}
