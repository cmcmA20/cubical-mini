{-# OPTIONS --safe #-}

module Algebra.Rig.Solver where

open import Foundations.Base

open import Meta.Marker
open import Meta.Underlying

open import Correspondences.Wellfounded

open import Data.Dec
import Data.Nat as ℕ
open import Data.Fin hiding (_≤_; _<_; _≥_; _>_; z≤; ≤-refl; ≤-trans)
open import Data.Empty
open import Data.Unit
open import Data.Sum

open import Algebra.Rig.Commutative

private variable
  ℓ ℓ′ ℓ″ : Level
  i j n m p j-1 i-1 : ℕ

module NatOrder where
  data _≤_ (n : ℕ) : ℕ → 𝒰 where
    ≤-refl : n ≤ n
    ≤-step : n ≤ m → n ≤ suc m

  _<_ _≥_ _>_ : (n m : ℕ) → 𝒰
  n < m = suc n ≤ m
  n ≥ m = m ≤ n
  n > m = m < n

  ≤-trans : n ≤ m → m ≤ p → n ≤ p
  ≤-trans n≤m ≤-refl = n≤m
  ≤-trans n≤m (≤-step m≤p) = ≤-step (≤-trans n≤m m≤p)

  z≤ : 0 ≤ n
  z≤ {(zero)} = ≤-refl
  z≤ {suc n}  = ≤-step z≤

  ≤-trans+ : n ≤ m → m < p → n ≤ p
  ≤-trans+ n≤m m<p = ≤-trans n≤m (≤-trans (≤-step ≤-refl) m<p)

  space : ∀ {n} → Fin n → ℕ
  space f = suc (go f)
    where
    go : ∀ {n} → Fin n → ℕ
    go {suc n}  fzero   = n
    go {suc _} (fsuc x) = go x

  space≤n : ∀ {n} (x : Fin n) → space x ≤ n
  space≤n {suc _}  fzero   = ≤-refl
  space≤n {suc _} (fsuc x) = ≤-step (space≤n x)

open NatOrder

mutual
  -- One or more
  --
  record Some (A : 𝒰 ℓ) : 𝒰 ℓ where
    inductive
    constructor _∷_
    field
      hd : A
      tl : Many A

  infixr 5 _∷_

  -- Zero or more
  --
  data Many (A : 𝒰 ℓ) : 𝒰 ℓ where
    Cons : Some A → Many A
    Nil  : Many A

open Some

record _⇓_ (S : ℕ → 𝒰 ℓ) (n : ℕ) : 𝒰 ℓ where
  constructor _⊐_
  field
    {scope} : ℕ
    body    : S scope
    scope≤n : scope ≤ n

open _⇓_
infixl 6 _⊐_

module Solve
    {ℓ‵}
    {A : 𝒰 ℓ‵}
    (_≡?_ : (a b : A) → Dec (a ＝ b))
    (R : Comm-rig-on A)
    -- (1≢0  : ¬ (CommutativeSemiring-on.𝟏 R ＝ CommutativeSemiring-on.𝟎 R))
  where

  𝟎   = R .fst .fst
  _+_ = R .fst .snd .fst
  𝟏   = R .fst .snd .snd .fst
  _*_ = R .fst .snd .snd .snd
  infixl 6 _+_
  infixl 7 _*_
  open module R = is-comm-rig (R .snd)

  module Base where

    mutual
      record PowIndex {ℓ} (C : 𝒰 ℓ) : 𝒰 ℓ where
        inductive
        pattern
        constructor _Δ_
        field
          coeff : C
          power : ℕ

      infixl 6 _Δ_

      data Poly : ℕ -> 𝒰 ℓ‵ where
        [_] : A → Poly 0
        Sum :
          (ks    : Some (Coeff n))
          {norm  : Norm ks}
                → Poly (suc n)

      record NonZero (n : ℕ) : 𝒰 ℓ‵ where
        inductive
        constructor _≢0
        field
          poly      : Poly ⇓ n
          {nonZero} : ¬ Zero poly

      infixl 6 _≢0

      Coeff : ℕ → 𝒰 ℓ‵
      Coeff n = PowIndex (NonZero n)

      Zero : Poly ⇓ n → 𝒰 ℓ‵
      Zero ([ x ]  ⊐ _) = x ＝ 𝟎
      Zero (Sum ks ⊐ _) = Lift _ ⊥

      Norm : Some (Coeff n) → 𝒰
      Norm ((_ Δ zero )  ∷ Cons _) = ⊤
      Norm ((_ Δ zero )  ∷ Nil)    = ⊥
      Norm ((_ Δ suc _ ) ∷ _)      = ⊤

    open PowIndex
    open NonZero

    zero? : (p : Poly ⇓ n) -> Dec (Zero p)
    zero? ([ x ] ⊐ _) with x ≡? 𝟎
    ... | yes z = yes z
    ... | no ¬z = no ¬z
    zero? (Sum ks ⊐ _) = no λ ()

    mutual
      -- Multiply head on x^n.
      --
      _^+_ : Some (Coeff n) → ℕ → Some (Coeff n)
      (ixs ^+ n) .hd .coeff = ixs .hd .coeff
      (ixs ^+ n) .hd .power = ixs .hd .power ℕ.+ n
      (ixs ^+ _) .tl        = ixs .tl

      -- Multiply head on x^n.
      --
      _^*_ : Many (Coeff n) → ℕ → Many (Coeff n)
      Cons x ^* x₁ = Cons (x ^+ x₁)
      Nil    ^* x₁ = Nil

    infix 5 _∷↓_
    _∷↓_ : PowIndex (Poly ⇓ n) → Many (Coeff n) → Many (Coeff n)
    (p Δ i ) ∷↓ ps with zero? p
    ... | yes z = ps ^* suc i
    ... | no ¬z = Cons ((_≢0 p {¬z} Δ i ) ∷ ps)

    _⊐↑_ : Poly ⇓ n → suc n ≤ m → Poly ⇓ m
    (xs ⊐ i≤n) ⊐↑ n<m = xs ⊐ ≤-trans+ i≤n n<m

    infixr 4 _⊐↓_
    _⊐↓_ : Many (Coeff m) → suc m ≤ n → Poly ⇓ n
    Nil                           ⊐↓ m<n = [ 𝟎 ] ⊐ z≤
    Cons (p ≢0 Δ i     ∷ Nil)     ⊐↓ m<n = p ⊐↑ m<n
    Cons (x    Δ zero  ∷ Cons xs) ⊐↓ m<n = Sum (x Δ zero  ∷ Cons xs) ⊐ m<n
    Cons (x    Δ suc i ∷ Cons xs) ⊐↓ m<n = Sum (x Δ suc i ∷ Cons xs) ⊐ m<n

    PolyF : ℕ → 𝒰 ℓ‵
    PolyF n = Poly ⇓ n × Many (Coeff n)

    Fold : ℕ → 𝒰 ℓ‵
    Fold n = PolyF n → PolyF n

    para : Fold n → Some (Coeff n) → Many (Coeff n)
    para f ((x ≢0) Δ i ∷ Cons xs) with f (x , para f xs)
    ... | y , ys = y Δ i ∷↓ ys
    para f ((x ≢0) Δ i ∷ Nil)     with f (x , Nil)
    ... | y , ys = y Δ i ∷↓ ys

    poly-map : (Poly ⇓ n → Poly ⇓ n) → Some (Coeff n) → Many (Coeff n)
    poly-map = para ∘ first

    data Order {n : ℕ} : (i≤n : i ≤ n) (j≤n : j ≤ n) → 𝒰 where
      lt : (i≤j-1 :     i   ≤ j-1) (j≤n   : suc j-1 ≤ n)   → Order (≤-trans (≤-step i≤j-1) j≤n) j≤n
      gt : (i≤n   : suc i-1 ≤ n)   (j≤i-1 :     j   ≤ i-1) → Order i≤n (≤-trans (≤-step j≤i-1) i≤n)
      eq : (i≤n   :     i   ≤ n)                           → Order i≤n i≤n


    order : (i≤n : i ≤ n) (j≤n : j ≤ n) → Order i≤n j≤n
    order ≤-refl      ≤-refl    = eq ≤-refl
    order ≤-refl     (≤-step b) = gt ≤-refl b
    order (≤-step a)  ≤-refl    = lt a ≤-refl
    order (≤-step a) (≤-step b) with order a b
    ... | lt i<j y = lt  i<j      (≤-step y)
    ... | gt x j<i = gt (≤-step x) j<i
    ... | eq x     = eq (≤-step x)

    data ℕ-ordering : (n m : ℕ) → 𝒰 where
      less    : ∀ n m → ℕ-ordering n (suc (n ℕ.+ m))
      equal   : ∀ n   → ℕ-ordering n n
      greater : ∀ n m → ℕ-ordering (suc (n ℕ.+ m)) n

    compare : ∀ n m → ℕ-ordering n m
    compare zero     zero   = equal   zero
    compare zero    (suc m) = less    zero m
    compare (suc n)  zero   = greater zero n
    compare (suc n) (suc m) with compare n m
    ... | less    .n m  = less    (suc n) m
    ... | equal   .n    = equal   (suc n)
    ... | greater .m m₁ = greater (suc m) m₁


    private variable
      x y z : A

    mutual
      _⊞_ : Poly ⇓ n → Poly ⇓ n → Poly ⇓ n
      (a ⊐ i≤n) ⊞ (b ⊐ j≤n) = ⊞-match (order i≤n j≤n) a b

      ⊞-match : {i≤n : i ≤ n} {j≤n : j ≤ n} (ord : Order i≤n j≤n) (a : Poly i) (b : Poly j) -> Poly ⇓ n
      ⊞-match (lt i≤j-1 j≤n) a                  (Sum b)            = ⊞-inj i≤j-1 a b               ⊐↓ j≤n
      ⊞-match (gt i≤n j≤i-1) (Sum a)            b                  = ⊞-inj j≤i-1 b a               ⊐↓ i≤n
      ⊞-match (eq i∷j≤n)     [ x ]              [ y ]              = [ x + y ]                     ⊐  i∷j≤n
      ⊞-match (eq i∷j≤n)     (Sum (x Δ i ∷ xs)) (Sum (y Δ j ∷ ys)) = ⊞-zip (compare i j) x xs y ys ⊐↓ i∷j≤n

      ⊞-inj : (i≤n : i ≤ n) (xs : Poly i) (ys : Some (Coeff n)) → Many (Coeff n)
      ⊞-inj i≤n xs (y ⊐ j≤n ≢0 Δ zero  ∷ ys) = ⊞-match (order i≤n j≤n) xs y Δ zero ∷↓               ys
      ⊞-inj i≤n xs (y          Δ suc j ∷ ys) = xs ⊐ i≤n Δ zero                     ∷↓ Cons (y Δ j ∷ ys)

      ⊞-coeffs : (xs ys : Many (Coeff n)) → Many (Coeff n)
      ⊞-coeffs (Cons (x Δ i ∷ xs)) ys = ⊞-zip-r x i xs ys
      ⊞-coeffs  Nil                ys = ys

      ⊞-zip : ∀ {p q n}
            → ℕ-ordering p q
            → NonZero n
            → Many (Coeff n)
            → NonZero n
            → Many (Coeff n)
            → Many (Coeff n)
      ⊞-zip (less    i k) x xs y ys = Cons (x Δ i ∷ ⊞-zip-r y k ys xs)
      ⊞-zip (greater j k) x xs y ys = Cons (y Δ j ∷ ⊞-zip-r x k xs ys)
      ⊞-zip (equal   i  ) x xs y ys = (x .poly ⊞ y .poly) Δ i ∷↓ ⊞-coeffs xs ys
      {-# INLINE ⊞-zip #-}

      ⊞-zip-r : (x : NonZero n) (i : ℕ) (xs ys : Many (Coeff n)) → Many (Coeff n)
      ⊞-zip-r x i xs Nil                 = Cons (x Δ i ∷ xs)
      ⊞-zip-r x i xs (Cons (y Δ j ∷ ys)) = ⊞-zip (compare i j) x xs y ys


    -- makeAcc : Wf ?
    -- makeAcc zero = ? -- rek λ { () }
    -- makeAcc (suc x) with makeAcc x
    -- ... | rek rs = rek λ where
    --   ≤-refl      → rek rs
    --   (≤-step x₁) → rek (λ x₂ → rs (≤-trans+ x₂ x₁))

    mutual
      ⊠-step′ : (ac : Acc _<_ n) (xs ys : Poly ⇓ n) → Poly ⇓ n
      ⊠-step′ ac (x ⊐ i≤n) = ⊠-step ac x i≤n

      ⊠-step : (ac : Acc _<_ n) (xs : Poly i) (i≤n : i ≤ n) (ys : Poly ⇓ n) → Poly ⇓ n
      ⊠-step ac [ x ] _  = ⊠-Κ ac x
      ⊠-step ac (Sum xs) = ⊠-⅀ ac xs

      ⊠-Κ : (ac : Acc _<_ n) (a : A) (xs : Poly ⇓ n) → Poly ⇓ n
      ⊠-Κ (acc ac) a ([ x ]  ⊐ i≤n) = [ a * x ] ⊐ i≤n
      ⊠-Κ (acc ac) a (Sum xs ⊐ i≤n) = {!!} -- ⊠-Κ-inj (ac i≤n) a xs ⊐↓ i≤n

      ⊠-Κ-inj : (ac : Acc _<_ n) (a : A) (xs : Some (Coeff n)) → Many (Coeff n)
      ⊠-Κ-inj ac a xs = poly-map (⊠-Κ ac a) xs

      ⊠-⅀ : (ac : Acc _<_ n) (xs : Some (Coeff i)) (i≤n : i < n) (ys : Poly ⇓ n) → Poly ⇓ n
      ⊠-⅀ (acc ac) xs i≤n ([ x ]  ⊐ j≤n) = {!!} -- ⊠-Κ-inj (ac i≤n) x xs ⊐↓ i≤n
      ⊠-⅀      ac  xs i≤n (Sum ys ⊐ j≤n) = ⊠-match ac (order i≤n j≤n) xs ys

      ⊠-match :
        (ac  : Acc _<_ n)
        {i≤n : i < n}
        {j≤n : j < n}
        (ord : Order i≤n j≤n)
        (xs  : Some (Coeff i))
        (ys  : Some (Coeff j))
            → Poly ⇓ n
      ⊠-match (acc ac) (lt i≤j-1 j≤n) xs ys = {!!} -- poly-map (⊠-⅀-inj (ac j≤n) i≤j-1 xs) ys ⊐↓ j≤n
      ⊠-match (acc ac) (gt i≤n j≤i-1) xs ys = {!!} -- poly-map (⊠-⅀-inj (ac i≤n) j≤i-1 ys) xs ⊐↓ i≤n
      ⊠-match (acc ac) (eq i∷j≤n)     xs ys = {!!} -- ⊠-coeffs (ac i∷j≤n)              xs  ys ⊐↓ i∷j≤n

      ⊠-coeffs : (ac : Acc _<_ n) (xs ys : Some (Coeff n)) → Many (Coeff n)
      ⊠-coeffs ac xs (y ≢0 Δ j ∷ Cons ys) = para     (⊠-cons  ac y ys) xs ^* j
      ⊠-coeffs ac xs (y ≢0 Δ j ∷ Nil)     = poly-map (⊠-step′ ac y)    xs ^* j

      ⊠-⅀-inj :
        (ac  : Acc _<_ n)
        (i≤n : i < n)
        (xs  : Some (Coeff i))
        (ys  : Poly ⇓ n)
            → Poly ⇓ n
      ⊠-⅀-inj (acc ac) i≤n xs ([ y ]  ⊐ j≤n) = {!!} -- ⊠-Κ-inj (ac i≤n) y xs ⊐↓ i≤n
      ⊠-⅀-inj  ac     i≤n xs (Sum ys ⊐ j≤n) = ⊠-match ac (order i≤n j≤n) xs ys

      ⊠-cons :
        (acc : Acc _<_ n)
        (y   : Poly ⇓ n)
        (ys  : Some (Coeff n))
            → Fold n
      ⊠-cons a y ys (x ⊐ j≤n , xs) =
        ⊠-step a x j≤n y , ⊞-coeffs (poly-map (⊠-step a x j≤n) ys) xs

--     infixl 7 _⊠_
--     _⊠_ : (a b : Poly ⇓ n) → Poly ⇓ n
--     _⊠_ = ⊠-step′ (makeAcc _)

--     κ : A → Poly ⇓ n
--     κ x = [ x ] ⊐ z≤

--     ι : Fin n → Poly ⇓ n
--     ι i = Sum ((_≢0 (κ 𝟏) {?} Δ 1) ∷ Nil) ⊐ space≤n i

--     ⊡-mult : ℕ → Poly ⇓ n → Poly ⇓ n
--     ⊡-mult zero    xs = xs
--     ⊡-mult (suc n) xs = ⊡-mult n xs ⊠ xs

--     _⊡_ : Poly ⇓ n → ℕ → Poly ⇓ n
--     xs ⊡ zero     = κ 𝟏
--     xs ⊡ suc zero = xs
--     xs ⊡ suc n    = ⊡-mult n xs

--   module Semantics where

--     open Base
--     open import Data.Vec renaming (_+_ to _⊹_)
--     import Data.Vec as Vec

--     drop : (i≤n : i ≤ n) (mem : Vec A n) → Vec A i
--     drop  ≤-refl           mem  = mem
--     drop (≤-step i≤n) (x ∷ mem) = drop i≤n mem

--     drop-1 : (i+1≤n : suc i ≤ n) (mem : Vec A n) → A × Vec A i
--     drop-1 i+1≤n mem with drop i+1≤n mem
--     ... | x ∷ xs = x , xs

--     _^_ : A → ℕ → A
--     x ^ zero  = 𝟏
--     x ^ 1     = x
--     x ^ suc n = (x ^ n) * x
--     infixl 50 _^_

--     _×′_ : ℕ → A → A
--     0     ×′ x = 𝟏
--     1     ×′ x = x
--     suc n ×′ x = (n ×′ x) * x

--     foo : ∀ a n → a ^ n ＝ n ×′ a
--     foo a zero = refl
--     foo a (suc zero) = refl
--     foo a (suc (suc n)) = ap (_* a) (foo a (suc n))

--     _*⟨_⟩^_ : A → A → ℕ → A
--     x *⟨ ρ ⟩^ zero  = x
--     x *⟨ ρ ⟩^ suc i = ρ ^ (suc i) * x

--     -- _*⟨_⟩^_ : A → A → ℕ → A
--     -- x *⟨ ρ ⟩^ zero  = x
--     -- x *⟨ ρ ⟩^ suc n = (ρ ^ suc n) * x

--     mutual
--       _⟦∷⟧_ :
--         (p    : Poly ⇓ n × Many (Coeff n))
--         (x∷xs : A × Vec A n)
--               → A
--       (x , Cons xs) ⟦∷⟧ (p , ps) = p * ⅀⟦ xs ⟧ (p , ps) + ⟦ x ⟧ ps
--       (x , Nil)     ⟦∷⟧ (p , ps) = ⟦ x ⟧ ps

--       ⅀⟦_⟧ : Some (Coeff n) → A × Vec A n → A
--       ⅀⟦ x ≢0 Δ i ∷ xs ⟧ (p , ps) = ((x , xs) ⟦∷⟧ (p , ps)) *⟨ p ⟩^ i

--       ⟦_⟧ : Poly ⇓ n → Vec A n → A
--       ⟦ [ x ]  ⊐ i≤n ⟧ p = x
--       ⟦ Sum xs ⊐ i≤n ⟧ p = ⅀⟦ xs ⟧ (drop-1 i≤n p)

--   module Lemmas where

--     open Base
--     open Semantics
--     open import Algebra.Monoid
--     open import Algebra.Monoid.Commutative
--     open import Meta.Marker
--     open import Data.Vec hiding (_+_)

--     pow-opt : ∀ x ρ i → x *⟨ ρ ⟩^ i ＝ (ρ ^ i) * x
--     pow-opt x ρ  zero   = ? -- sym (*-is-monoid .idl)
--     pow-opt x ρ (suc i) = refl

--     pow-add : ∀ x y i j → (y ^ suc j) * (x *⟨ y ⟩^ i) ＝ x *⟨ y ⟩^ (i ⊹ suc j)
--     pow-add x y zero    j = refl
--     pow-add x y (suc i) j = go x y i j
--       where
--         go : ∀ x y i j → (y ^ suc j) * ((y ^ suc i) * x) ＝ y ^ suc (i ⊹ suc j) * x
--         go x y zero j = ? -- associative *-is-monoid _ _ _
--         go x y (suc i) j =
--           (y ^ suc j) * ⌜ y ^ (suc i) *  y * x ⌝ ＝⟨ ? ⟩
-- --           (y ^ suc j) * ⌜ y ^ (suc i) *  y * x ⌝ ＝⟨ ap! (sym (associative *-is-monoid _ _ _)) ⟩
--           (y ^ suc j) *  (y ^ (suc i) * (y * x)) ＝⟨ go (y * x) y i j ⟩
--            y ^ suc     (i ⊹ suc j)    * (y * x)  ＝⟨ ? ⟩
-- --                      y ^ suc     (i ⊹ suc j)    * (y * x)  ＝⟨ associative *-is-monoid _ y x ⟩
--            y ^ suc (suc i ⊹ suc j)         * x   ∎

--     open import Data.Nat.Properties using (+-zeror)

--     pow-hom :
--       (i  : ℕ)
--       (xs : Some (Coeff n))
--       (ρ  : A)
--       (ρs : Vec A n)
--           → ⅀⟦ xs      ⟧ (ρ , ρs) *⟨ ρ ⟩^ i
--           ＝ ⅀⟦ xs ^+ i ⟧ (ρ , ρs)
--     pow-hom zero xs ρ ρs =
--       left *⟨ ρ ⟩^ ⌜ right ⌝    ＝⟨ ? ⟩
-- --             left *⟨ ρ ⟩^ ⌜ right ⌝    ＝⟨ ap! (sym (+-zeror right)) ⟩
--       left *⟨ ρ ⟩^  (right ⊹ 0) ∎
--       where
--         left = (xs .hd .PowIndex.coeff .NonZero.poly , xs .tl) ⟦∷⟧ (ρ , ρs)
--         right = xs .hd .PowIndex.power

--     pow-hom (suc i) (x ≢0 Δ j ∷ xs) ρ ρs =
--       ρ ^ (suc i) * (((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ j)          ＝⟨ pow-add _ _ j _ ⟩
--                      ((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ (j ⊹ suc i) ∎


--     open import Data.Vec.Operations.Inductive as Vec hiding (_+_)

--     pow-mul-cong : ∀ {x y} → x ＝ y → ∀ ρ i → x *⟨ ρ ⟩^ i ＝ y *⟨ ρ ⟩^ i
--     pow-mul-cong x＝y ρ zero    = x＝y
--     pow-mul-cong {x} {y} x＝y ρ (suc i) =
--       ρ ^ suc i * ⌜ x ⌝ ＝⟨ ap! x＝y ⟩
--       ρ ^ suc i *   y   ∎

--     zero-hom : ∀ {n} (p : Poly ⇓ n) → Zero p → (ρs : Vec A n) → 𝟎 ＝ ⟦ p ⟧ ρs
--     zero-hom ([ x₁ ] ⊐ i≤n) p≡𝟎 ρs = sym p≡𝟎

--     pow-suc : ∀ x i → x ^ suc i ＝ x * x ^ i
--     pow-suc x zero = ? -- sym (*-is-monoid .idr)
--     pow-suc x (suc i) = ? -- sym (is-abelian-monoid.commutes *-is-abelian-monoid)

--     pow-sucʳ : ∀ x i → x ^ suc i ＝ x ^ i * x
--     pow-sucʳ x zero = ? -- sym (*-is-monoid .idl)
--     pow-sucʳ x (suc i) = refl

--     ⅀?⟦_⟧ : ∀ {n} (xs : Many (Coeff n)) → A × Vec A n → A
--     ⅀?⟦ Cons xs ⟧   = ⅀⟦ xs ⟧
--     ⅀?⟦ Nil     ⟧ _ = 𝟎

--     _⟦∷⟧?_ : ∀ {n} (x : Poly ⇓ n × Many (Coeff n)) → A × Vec A n → A
--     (x , xs) ⟦∷⟧? (ρ , ρs) = ρ * ⅀?⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs

--     ⅀?-hom : ∀ {n} (xs : Some (Coeff n)) → ∀ ρ → ⅀?⟦ Cons xs ⟧ ρ ＝ ⅀⟦ xs ⟧ ρ
--     ⅀?-hom _ _ = refl

--     ⟦∷⟧?-hom : ∀ {n} (x : Poly ⇓ n) → ∀ xs ρ ρs → (x , xs) ⟦∷⟧? (ρ , ρs) ＝ (x , xs) ⟦∷⟧ (ρ , ρs)
--     ⟦∷⟧?-hom x (Cons x₁) ρ ρs = refl
--     ⟦∷⟧?-hom x Nil ρ ρs =
--       ⌜ ρ * 𝟎 ⌝ + ⟦ x ⟧ ρs ＝⟨ ? ⟩
-- --            ⌜ ρ * 𝟎 ⌝ + ⟦ x ⟧ ρs ＝⟨ ap! 𝟎-absorbs-left ⟩
--             𝟎   + ⟦ x ⟧ ρs ＝⟨ ? ⟩
-- --                         𝟎   + ⟦ x ⟧ ρs ＝⟨ +-is-abelian-monoid .is-abelian-monoid.idl ⟩
--                   ⟦ x ⟧ ρs ∎

--     pow′-hom : ∀ {n} i (xs : Many (Coeff n)) → ∀ ρ ρs → ((⅀?⟦ xs ⟧ (ρ , ρs)) *⟨ ρ ⟩^ i) ＝ (⅀?⟦ xs ^* i ⟧ (ρ , ρs))
--     pow′-hom  i     (Cons xs) ρ ρs = pow-hom i xs ρ ρs
--     pow′-hom  zero   Nil      ρ ρs = refl
--     pow′-hom (suc i) Nil      ρ ρs = ? -- 𝟎-absorbs-left

--     ∷↓-hom-0 : ∀ {n} (x : Poly ⇓ n) → ∀ xs ρ ρs → ⅀?⟦ x Δ 0 ∷↓ xs ⟧ (ρ , ρs) ＝ (x , xs) ⟦∷⟧ (ρ , ρs)
--     ∷↓-hom-0 x xs ρ ρs with zero? x
--     ∷↓-hom-0 x xs ρ ρs | no ¬z = refl
--     ∷↓-hom-0 x Nil ρ ρs | yes z = zero-hom x z ρs
--     ∷↓-hom-0 x (Cons xs) ρ ρs | yes z =
--       ⅀⟦ xs ^+ 1 ⟧ (ρ , ρs)             ＝⟨ sym (pow-hom 1 xs ρ ρs) ⟩
--       ρ * ⅀⟦ xs ⟧  (ρ , ρs)             ＝⟨ ? ⟩
-- --            ρ * ⅀⟦ xs ⟧  (ρ , ρs)             ＝⟨ sym (+-is-abelian-monoid .is-abelian-monoid.idr) ⟩
--       (ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⌜ 𝟎 ⌝)    ＝⟨ ap! (zero-hom x z ρs) ⟩
--       (ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs) ∎

--     ∷↓-hom-s : ∀ {n} (x : Poly ⇓ n) → ∀ i xs ρ ρs → ⅀?⟦ (x Δ suc i) ∷↓ xs ⟧ (ρ , ρs) ＝ (ρ ^ suc i) * ((x , xs) ⟦∷⟧ (ρ , ρs))
--     ∷↓-hom-s x i xs ρ ρs with zero? x
--     ∷↓-hom-s x i xs ρ ρs | no ¬p = refl
--     ∷↓-hom-s x i Nil ρ ρs | yes p =
--       𝟎                    ＝⟨ ? ⟩
-- --            𝟎                    ＝⟨ sym 𝟎-absorbs-left ⟩
--       ρ ^ suc i * ⌜ 𝟎 ⌝    ＝⟨ ap! (zero-hom x p ρs) ⟩
--       ρ ^ suc i * ⟦ x ⟧ ρs ∎

--     ∷↓-hom-s x i (Cons xs) ρ ρs | yes p =
--       ⅀⟦ xs ^+ (suc (suc i)) ⟧    (ρ , ρs)             ＝⟨ sym (pow-hom (suc (suc i)) xs ρ ρs) ⟩
--       (ρ ^ suc (suc i)) * ⅀⟦ xs ⟧ (ρ , ρs)             ＝⟨ ? ⟩
-- --            (ρ ^ suc (suc i)) * ⅀⟦ xs ⟧ (ρ , ρs)             ＝⟨ sym (is-abelian-monoid.associative *-is-abelian-monoid _ _ _) ⟩
--       (ρ ^ suc i) * ⌜ ρ * ⅀⟦ xs ⟧ (ρ , ρs) ⌝           ＝⟨ ? ⟩
-- --             (ρ ^ suc i) * ⌜ ρ * ⅀⟦ xs ⟧ (ρ , ρs) ⌝           ＝⟨ ap! (sym (+-is-abelian-monoid .is-abelian-monoid.idr)) ⟩
--       (ρ ^ suc i) *  (ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⌜ 𝟎 ⌝)    ＝⟨ ap! (zero-hom x p ρs) ⟩
--       (ρ ^ suc i) *  (ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs) ∎

--     ∷↓-hom : ∀ {n}
--        → (x : Poly ⇓ n)
--        → ∀ i xs ρ ρs
--        → ⅀?⟦ x Δ i ∷↓ xs ⟧ (ρ , ρs) ＝ ρ ^ i * ((x , xs) ⟦∷⟧ (ρ , ρs))
--     ∷↓-hom x zero xs ρ ρs =
--       _ ＝⟨ ∷↓-hom-0 x xs ρ ρs ⟩
--       _ ＝⟨ ? ⟩
-- --             _ ＝⟨ sym (*-is-monoid .idl) ⟩
--       _ ∎
--     ∷↓-hom x (suc i) xs ρ ρs = ∷↓-hom-s x i xs ρ ρs

--     ⟦∷⟧-hom : ∀ {n}
--        → (x : Poly ⇓ n)
--        → (xs : Many (Coeff n))
--        → ∀ ρ ρs → (x , xs) ⟦∷⟧ (ρ , ρs) ＝ ρ * ⅀?⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs
--     ⟦∷⟧-hom x (Cons xs) ρ ρs = refl
--     ⟦∷⟧-hom x Nil ρ ρs =
--                 ⟦ x ⟧ ρs ＝⟨ ? ⟩
-- --                                 ⟦ x ⟧ ρs ＝⟨ sym (+-is-abelian-monoid .is-abelian-monoid.idl) ⟩
--          ⌜ 𝟎 ⌝ + ⟦ x ⟧ ρs ＝⟨ ? ⟩
-- --                ⌜ 𝟎 ⌝ + ⟦ x ⟧ ρs ＝⟨ ap! (sym 𝟎-absorbs-left) ⟩
--       ρ * 𝟎   + ⟦ x ⟧ ρs ∎

--     ⅀-⊐↑-hom : ∀ {i n m}
--          → (xs : Some (Coeff i))
--          → (si≤n : suc i ≤ n)
--          → (sn≤m : suc n ≤ m)
--          → ∀ ρ
--          → ⅀⟦ xs ⟧ (drop-1 (≤-trans+ si≤n sn≤m) ρ)
--          ＝ ⅀⟦ xs ⟧ (drop-1 si≤n (snd (drop-1 sn≤m ρ)))
--     ⅀-⊐↑-hom xs si≤n  ≤-refl       (_ ∷ _) = refl
--     ⅀-⊐↑-hom xs si≤n (≤-step sn≤m) (_ ∷ ρ) = ⅀-⊐↑-hom xs si≤n sn≤m ρ

--     ⊐↑-hom : ∀ {n m}
--        → (x : Poly ⇓ n)
--        → (sn≤m : suc n ≤ m)
--        → ∀ ρ
--        → ⟦ x ⊐↑ sn≤m ⟧ ρ ＝ ⟦ x ⟧ (snd (drop-1 sn≤m ρ))
--     ⊐↑-hom ([ x ]  ⊐ i≤n) _ _ = refl
--     ⊐↑-hom (Sum ks ⊐ i≤n)     = ⅀-⊐↑-hom ks i≤n

--     trans-join-coeffs-hom : ∀ {i j-1 n}
--       → (i≤j-1 : suc i ≤ j-1)
--       → (j≤n   : suc j-1 ≤ n)
--       → (xs : Some (Coeff i))
--       → ∀ ρ
--       → ⅀⟦ xs ⟧ (drop-1 i≤j-1 (snd (drop-1 j≤n ρ)))
--       ＝ ⅀⟦ xs ⟧ (drop-1 (≤-trans (≤-step i≤j-1) j≤n) ρ)
--     trans-join-coeffs-hom i≤j-1  ≤-refl      xs (_ ∷ _) = refl
--     trans-join-coeffs-hom i≤j-1 (≤-step j≤n) xs (_ ∷ ρ) = trans-join-coeffs-hom i≤j-1 j≤n xs _

--     trans-join-hom : ∀ {i j-1 n}
--       → (i≤j-1 : i ≤ j-1)
--       → (j≤n   : suc j-1 ≤ n)
--       → (x : Poly i)
--       → ∀ ρ
--       → ⟦ x ⊐ i≤j-1 ⟧ (snd (drop-1 j≤n ρ)) ＝ ⟦ x ⊐ (≤-trans (≤-step i≤j-1) j≤n) ⟧ ρ
--     trans-join-hom i≤j-1 j≤n [ x ] _  = refl
--     trans-join-hom i≤j-1 j≤n (Sum ks) = trans-join-coeffs-hom i≤j-1 j≤n ks

--     ⊐↓-hom : ∀ {n m}
--           → (xs : Many (Coeff n))
--           → (sn≤m : suc n ≤ m)
--           → ∀ ρ
--           → ⟦ xs ⊐↓ sn≤m ⟧ ρ ＝ ⅀?⟦ xs ⟧ (drop-1 sn≤m ρ)
--     ⊐↓-hom  Nil                            sn≤m _  = refl
--     ⊐↓-hom (Cons (x₁   Δ zero  ∷ Cons xs)) sn≤m _  = refl
--     ⊐↓-hom (Cons (x ≢0 Δ suc j ∷ xs))      sn≤m _  = {! refl !}
--     ⊐↓-hom (Cons (x ≢0 Δ zero  ∷ Nil))     sn≤m ρs =
--       let (ρ , ρs′) = drop-1 sn≤m ρs
--       in
--         ⟦ x ⊐↑ sn≤m ⟧ ρs
--       ＝⟨ ⊐↑-hom x sn≤m ρs ⟩
--         ⟦ x ⟧ ρs′
--       ∎


--     drop-1⇒lookup : ∀ {n} (i : Fin n) (ρs : Vec A n) →
--                 fst (drop-1 (space≤n i) ρs) ＝ Vec.lookup ρs i
--     drop-1⇒lookup {suc n}  fzero   (x ∷ ρs) = refl
--     drop-1⇒lookup {suc n} (fsuc i) (x ∷ ρs) = drop-1⇒lookup i ρs

--     poly-foldR : ∀ {n} ρ ρs
--         → ([f] : Fold n)
--         → (f : A → A)
--         → (∀ {x y} → x ＝ y → f x ＝ f y)
--         → (∀ x y → x * f y ＝ f (x * y))
--         → (∀ y {ys} zs → ⅀?⟦ ys ⟧ (ρ , ρs) ＝ f (⅀?⟦ zs ⟧ (ρ , ρs)) → [f] (y , ys) ⟦∷⟧? (ρ , ρs) ＝ f ((y , zs) ⟦∷⟧? (ρ , ρs)) )
--         → (f 𝟎 ＝ 𝟎)
--         → ∀ xs
--         → ⅀?⟦ para [f] xs ⟧ (ρ , ρs) ＝ f (⅀⟦ xs ⟧ (ρ , ρs))
--     poly-foldR ρ ρs f e cng dist step base (x ≢0 Δ suc i ∷ Nil) =
--       let y,ys   = f (x , Nil)
--           y , ys = y,ys
--       in
--          ⅀?⟦ y Δ suc i ∷↓ ys ⟧ (ρ , ρs) ＝⟨ ∷↓-hom-s y i ys ρ ρs ⟩
--          (ρ ^ suc i) * ⌜    (y , ys)  ⟦∷⟧  (ρ , ρs)  ⌝ ＝⟨ ap! (sym (⟦∷⟧?-hom y ys ρ ρs)) ⟩
--          (ρ ^ suc i) * ⌜    (y , ys)  ⟦∷⟧? (ρ , ρs)  ⌝ ＝⟨ ap! (step x Nil (sym base)) ⟩
--          (ρ ^ suc i) * ⌜ e ((x , Nil) ⟦∷⟧? (ρ , ρs)) ⌝ ＝⟨ ap! (cng (⟦∷⟧?-hom x Nil ρ ρs)) ⟩
--          (ρ ^ suc i) *   e ((x , Nil) ⟦∷⟧  (ρ , ρs))   ＝⟨ dist _ _   ⟩
--       e ((ρ ^ suc i) *     ((x , Nil) ⟦∷⟧  (ρ , ρs)))  ∎

--     poly-foldR ρ ρs f e cng dist step base (x ≢0 Δ suc i ∷ Cons xs) =
--       let ys     = para f xs
--           y,zs   = f (x , ys)
--           y , zs = y,zs
--       in
--           ⅀?⟦ y Δ suc i ∷↓ zs ⟧ (ρ , ρs) ＝⟨ ∷↓-hom-s y i zs ρ ρs  ⟩
--           (ρ ^ suc i) * ⌜    (y ,       zs)   ⟦∷⟧  (ρ , ρs)  ⌝ ＝⟨ ap! (sym (⟦∷⟧?-hom y zs ρ ρs)) ⟩
--           (ρ ^ suc i) * ⌜    (y ,       zs)   ⟦∷⟧? (ρ , ρs)  ⌝ ＝⟨ ap! (step x (Cons xs) (poly-foldR ρ ρs f e cng dist step base xs)) ⟩
--           (ρ ^ suc i) * ⌜ e ((x , (Cons xs )) ⟦∷⟧? (ρ , ρs)) ⌝ ＝⟨ ap! (cng (⟦∷⟧?-hom x (Cons xs) ρ ρs)) ⟩
--           (ρ ^ suc i) *   e ((x , (Cons xs )) ⟦∷⟧  (ρ , ρs))   ＝⟨ dist _ _   ⟩
--         e (ρ ^ suc i  *     ((x , (Cons xs )) ⟦∷⟧  (ρ , ρs)))  ∎
--       -- {!   !} ∎

--     poly-foldR ρ ρs f e cng dist step base (x ≢0 Δ ℕ.zero ∷ Nil) =
--       let y,zs   = f (x , Nil)
--           y , zs = y,zs
--       in
--         ⅀?⟦ y Δ ℕ.zero ∷↓ zs ⟧   (ρ , ρs)  ＝⟨ ∷↓-hom-0 y zs ρ ρs ⟩
--                  ((y , zs)  ⟦∷⟧  (ρ , ρs)) ＝⟨ sym (⟦∷⟧?-hom y zs ρ ρs) ⟩
--                  ((y , zs)  ⟦∷⟧? (ρ , ρs)) ＝⟨ step x Nil (sym base) ⟩
--                e ((x , Nil) ⟦∷⟧? (ρ , ρs)) ＝⟨ cng (⟦∷⟧?-hom x Nil ρ ρs) ⟩
--                e ((x , Nil) ⟦∷⟧  (ρ , ρs)) ∎

--     poly-foldR ρ ρs f e cng dist step base (x ≢0 Δ ℕ.zero ∷ Cons xs) =
--       let ys = para f xs
--           y,zs = f (x , ys)
--           y , zs = y,zs
--       in
--             ⅀?⟦ y Δ ℕ.zero ∷↓ zs ⟧ (ρ , ρs)  ＝⟨ ∷↓-hom-0 y zs ρ ρs ⟩
--         ((y , zs)         ⟦∷⟧      (ρ , ρs)) ＝⟨ sym (⟦∷⟧?-hom y zs ρ ρs) ⟩
--         ((y , zs)         ⟦∷⟧?     (ρ , ρs)) ＝⟨ step x (Cons xs ) (poly-foldR ρ ρs f e cng dist step base xs) ⟩
--       e ((x , (Cons xs )) ⟦∷⟧      (ρ , ρs)) ＝⟨ cng (⟦∷⟧?-hom x (Cons xs ) ρ ρs) ⟩
--       e ((x , (Cons xs )) ⟦∷⟧      (ρ , ρs)) ∎


--     poly-mapR : ∀ {n} ρ ρs
--           → ([f] : Poly ⇓ n → Poly ⇓ n)
--           → (f : A → A)
--           → (∀ {x y} → x ＝ y → f x ＝ f y)
--           → (∀ x y → x * f y ＝ f (x * y))
--           → (∀ x y → f (x + y) ＝ f x + f y)
--           → (∀ y → ⟦ [f] y ⟧ ρs ＝ f (⟦ y ⟧ ρs) )
--           → (f 𝟎 ＝ 𝟎)
--           → ∀ xs
--           → ⅀?⟦ poly-map [f] xs ⟧ (ρ , ρs) ＝ f (⅀⟦ xs ⟧ (ρ , ρs))
--     poly-mapR ρ ρs [f] f cng *-dist +-dist step′ base xs = ? -- poly-foldR ρ ρs [ [f] , id ]ₚ f cng *-dist step base xs
--       where
--       step : ∀ y {ys} zs
--         →                 ⅀?⟦ ys ⟧     (ρ , ρs)  ＝ f  (⅀?⟦ zs ⟧     (ρ , ρs))
--         → ? ⟦∷⟧? (ρ , ρs) ＝ f ((y , zs) ⟦∷⟧? (ρ , ρs))
-- --                 → ([ [f] , id ]ₚ (y , ys)) ⟦∷⟧? (ρ , ρs) ＝ f ((y , zs) ⟦∷⟧? (ρ , ρs))
--       step y {ys} zs ys≋zs =
--          {- ((*≫ ys≋zs) ⟨ trans ⟩ *-dist ρ _) ⟨ +-cong ⟩ step′ y -}
--         ? ⟦∷⟧? (ρ , ρs) ＝⟨⟩
-- --                 ([ [f] , id ]ₚ (y , ys)) ⟦∷⟧? (ρ , ρs) ＝⟨⟩
--            ρ * ⌜  ⅀?⟦ ys ⟧ (ρ , ρs)  ⌝ +   ⟦ [f] y ⟧ ρs   ＝⟨ ap! ys≋zs ⟩
--         ⌜  ρ * f (⅀?⟦ zs ⟧ (ρ , ρs)) ⌝ +   ⟦ [f] y ⟧ ρs   ＝⟨ ap! (*-dist _ _) ⟩
--         f (ρ *    ⅀?⟦ zs ⟧ (ρ , ρs))   + ⌜ ⟦ [f] y ⟧ ρs ⌝ ＝⟨ ap! (step′ _) ⟩
--         f (ρ *    ⅀?⟦ zs ⟧ (ρ , ρs))   + f (⟦ y ⟧ ρs)     ＝⟨ sym (+-dist _ _) ⟩
--         f (ρ *    ⅀?⟦ zs ⟧ (ρ , ρs)    +    ⟦ y ⟧ ρs)     ＝⟨ +-dist _ _ ⟩
--         f (ρ *    ⅀?⟦ zs ⟧ (ρ , ρs))   + f (⟦ y ⟧ ρs)     ＝⟨ sym (+-dist _ _) ⟩
--         f ((y , zs) ⟦∷⟧? (ρ , ρs))                        ∎

--   module Addition where

--     open Base
--     open Semantics
--     open Lemmas

--     open import Data.Vec hiding (_+_)

--     mutual
--       ⊞-hom : ∀ {n} (xs ys : Poly ⇓ n) →
--           ∀ ρ → ⟦ xs ⊞ ys ⟧ ρ ＝ ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ
--       ⊞-hom = {!   !}

--       ⊞-match-hom : ∀ {i j n} {i≤n : i ≤ n} {j≤n : j ≤ n}
--                     (i-cmp-j : Order i≤n j≤n)
--                     (xs : Poly i) (ys : Poly j) →
--                     ∀ ρ → ⟦ ⊞-match i-cmp-j xs ys ⟧ ρ ＝ ⟦ xs ⊐ i≤n ⟧ ρ + ⟦ ys ⊐ j≤n ⟧ ρ
--       ⊞-match-hom = {!   !}

--       ⊞-inj-hom : ∀ {i k}
--             → (i≤k : i ≤ k)
--             → (x : Poly i)
--             → (ys : Some (Coeff k))
--             → (ρ : A)
--             → (Ρ : Vec A k)
--             → ⅀?⟦ ⊞-inj i≤k x ys ⟧ (ρ , Ρ) ＝ ⟦ x ⊐ i≤k ⟧ Ρ + ⅀⟦ ys ⟧ (ρ , Ρ)
--       ⊞-inj-hom = {!   !}

--       ⊞-coeffs-hom : ∀ {n} (xs : Many (Coeff n)) (ys : Many (Coeff n)) →
--                   ∀ ρ → ⅀?⟦ ⊞-coeffs xs ys ⟧ ρ ＝ ⅀?⟦ xs ⟧ ρ + ⅀?⟦ ys ⟧ ρ
--       ⊞-coeffs-hom = {!   !}

--       ⊞-zip-hom : ∀ {n i j}
--             → (c : ℕ-ordering i j)
--             → (x : NonZero n)
--             → (xs : Many (Coeff n))
--             → (y : NonZero n)
--             → (ys : Many (Coeff n))
--             → ∀ ρ → ⅀?⟦ ⊞-zip c x xs y ys ⟧ ρ ＝ ⅀⟦ x Δ i ∷ xs ⟧ ρ + ⅀⟦ y Δ j ∷ ys ⟧ ρ
--       ⊞-zip-hom = {!   !}

--       ⊞-zip-r-step-hom : ∀ {n} j k
--         → (x : NonZero n)
--         → (xs : Many (Coeff n))
--         → (y : NonZero n)
--         → (ys : Many (Coeff n))
--         → ∀ ρ
--         →  ⅀⟦ y Δ      j      ∷ ⊞-zip-r x k xs ys ⟧ ρ
--         ＝ ⅀⟦ x Δ suc (j ⊹ k) ∷             xs    ⟧ ρ
--         +  ⅀⟦ y Δ      j      ∷                ys ⟧ ρ
--       ⊞-zip-r-step-hom = {!   !}

--       ⊞-zip-r-hom : ∀ {n} i
--         → (x : NonZero n)
--         → (xs ys : Many (Coeff n))
--         → (Ρ : A × Vec A n)
--         → ⅀?⟦ ⊞-zip-r x i xs ys ⟧ Ρ ＝ ⅀⟦ x Δ i ∷ xs ⟧ Ρ + ⅀?⟦ ys ⟧ Ρ
--       ⊞-zip-r-hom = {!   !}

--   module Reasoning where

--     open Base
--     open import Meta.Marker

--     infixr 1 ≪+_ +≫_ ≪*_ *≫_
--     infixr 0 _⊙_

--     _⟨_⟩_ :
--       {ℓ ℓ′ ℓ″ : _}
--       {A : 𝒰 ℓ}
--       {B : 𝒰 ℓ′}
--       {C : 𝒰 ℓ″}
--       (a : A)
--       (f : A → B → C)
--       (b : B)
--          → C
--     a ⟨ f ⟩ b = f a b

--     ≪+_ : ∀ {x₁ x₂ y} → x₁ ＝ x₂ → x₁ + y ＝ x₂ + y
--     ≪+ prf = ⌜ _ ⌝ + _ ＝⟨ ap! prf ⟩ _ ∎
--     {-# INLINE ≪+_ #-}

--     +≫_ : ∀ {x y₁ y₂} → y₁ ＝ y₂ → x + y₁ ＝ x + y₂
--     +≫ prf  = _ + ⌜ _ ⌝ ＝⟨ ap! prf ⟩ _ ∎
--     {-# INLINE +≫_ #-}

--     ≪*_ : ∀ {x₁ x₂ y} → x₁ ＝ x₂ → x₁ * y ＝ x₂ * y
--     ≪* prf = ⌜ _ ⌝ * _ ＝⟨ ap! prf ⟩ _ ∎
--     {-# INLINE ≪*_ #-}

--     *≫_ : ∀ {x y₁ y₂} → y₁ ＝ y₂ → x * y₁ ＝ x * y₂
--     *≫ prf = _ * ⌜ _ ⌝ ＝⟨ ap! prf ⟩ _ ∎
--     {-# INLINE *≫_ #-}

--     -- transitivity as an operator
--     _⊙_ : ∀ {x y z : A} → x ＝ y → y ＝ z → x ＝ z
--     _⊙_ = _∙_
--     {-# INLINE _⊙_ #-}

--     +-cong : {x y u v : A} → x ＝ y → u ＝ v → x + u ＝ y + v
--     +-cong x=y u=v =
--       ⌜ _ ⌝ +   _   ＝⟨ ap! x=y ⟩
--         _   + ⌜ _ ⌝ ＝⟨ ap! u=v ⟩
--         _ ∎

--     *-cong : {x y u v : A} → x ＝ y → u ＝ v → x * u ＝ y * v
--     *-cong x=y u=v =
--       ⌜ _ ⌝ *   _   ＝⟨ ap! x=y ⟩
--         _   * ⌜ _ ⌝ ＝⟨ ap! u=v ⟩
--         _ ∎

--     open import Algebra.Monoid
--     open import Algebra.Monoid.Commutative

--     -- +-assoc : {x y z : A} → (x + y) + z ＝ x + (y + z)
--     -- +-assoc = sym $ is-abelian-monoid.associative +-is-abelian-monoid _ _ _

--     -- *-assoc : {x y z : A} → (x * y) * z ＝ x * (y * z)
--     -- *-assoc = sym $ associative *-is-monoid _ _ _

--     -- +-comm : {x y : A} → x + y ＝ y + x
--     -- +-comm = is-abelian-monoid.commutes +-is-abelian-monoid

--     -- *-comm : {x y : A} → x * y ＝ y * x
--     -- *-comm = is-abelian-monoid.commutes *-is-abelian-monoid


--   module Multiplication where

--     open Base
--     open Semantics
--     open Lemmas
--     open Addition
--     open import Algebra.Monoid
--     open import Algebra.Monoid.Commutative
--     open import Data.Vec hiding (_+_)
--     open import Meta.Marker

--     reassoc : ∀ {y} x z → x * (y * z) ＝ y * (x * z)
--     reassoc {y} x z =
--         x * (y   * z) ＝⟨ associative *-is-monoid _ _ _ ⟩
--       ⌜ x *  y ⌝ * z  ＝⟨ ap! (is-abelian-monoid.commutes *-is-abelian-monoid) ⟩
--        (y *  x)  * z  ＝⟨ sym (associative *-is-monoid _ _ _) ⟩
--         y * (x   * z) ∎

--     mutual
--       ⊠-step′-hom : ∀ {n} → (a : Acc n) → (xs ys : Poly ⇓ n) → ∀ ρ → ⟦ ⊠-step′ a xs ys ⟧ ρ ＝ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
--       ⊠-step′-hom a (x ⊐ p) = ⊠-step-hom a x p

--       ⊠-step-hom : ∀ {i n}
--         → (a : Acc n)
--         → (xs : Poly i)
--         → (i≤n : i ≤ n)
--         → (ys : Poly ⇓ n)
--         → ∀ ρ → ⟦ ⊠-step a xs i≤n ys ⟧ ρ ＝ ⟦ xs ⊐ i≤n ⟧ ρ * ⟦ ys ⟧ ρ
--       ⊠-step-hom a [ x ]    i≤n = ⊠-Κ-hom a x
--       ⊠-step-hom a (Sum xs) i≤n = ⊠-⅀-hom a xs i≤n

--       ⊠-Κ-hom : ∀ {n}
--         → (a : Acc n)
--         → ∀ x
--         → (ys : Poly ⇓ n)
--         → ∀ ρ
--         → ⟦ ⊠-Κ a x ys ⟧ ρ ＝ x * ⟦ ys ⟧ ρ
--       ⊠-Κ-hom (rek _)  x ([ y ]  ⊐ i≤n) ρ = refl -- *-homo x y
--       ⊠-Κ-hom (rek wf) x (Sum xs ⊐ i≤n) ρ =
--           ⟦ ⊠-Κ-inj (wf i≤n) x xs ⊐↓        i≤n ⟧ ρ  ＝⟨ ⊐↓-hom (⊠-Κ-inj (wf i≤n) x xs) i≤n ρ ⟩
--         ⅀?⟦ ⊠-Κ-inj (wf i≤n) x xs ⟧ (drop-1 i≤n   ρ) ＝⟨ ⊠-Κ-inj-hom (wf i≤n) x xs (drop-1 i≤n ρ) ⟩
--                         x * ⅀⟦ xs ⟧ (drop-1 i≤n   ρ) ∎

--       ⊠-Κ-inj-hom : ∀ {n}
--         → (a : Acc n)
--         → (x : A)
--         → (xs : Some (Coeff n))
--         → ∀ ρ
--         → ⅀?⟦ ⊠-Κ-inj a x xs ⟧ ρ ＝ x * ⅀⟦ xs ⟧ ρ
--       ⊠-Κ-inj-hom {n} a x xs (ρ , Ρ) =
--         poly-mapR
--           ρ
--           Ρ
--           (⊠-Κ a x)
--           (x *_)
--           (*-cong refl)
--           reassoc
--           (λ _ _ → *-distributes-over-+-right)
--           (λ ys → ⊠-Κ-hom a x ys Ρ)
--           𝟎-absorbs-left
--           xs

--       ⊠-⅀-hom : ∀ {i n}
--           → (a : Acc n)
--           → (xs : Some (Coeff i))
--           → (i<n : i < n)
--           → (ys : Poly ⇓ n)
--           → ∀ ρ
--           → ⟦ ⊠-⅀ a xs i<n ys ⟧ ρ ＝ ⅀⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ ys ⟧ ρ
--       ⊠-⅀-hom (rek wf) xs i<n (Sum ys ⊐ j≤n) = ⊠-match-hom (rek wf) (order i<n j≤n) xs ys
--       ⊠-⅀-hom (rek wf) xs i<n ([ y ] ⊐ _) ρ =
--           ⟦ ⊠-Κ-inj (wf i<n) y xs ⊐↓        i<n ⟧ ρ      ＝⟨ ⊐↓-hom (⊠-Κ-inj (wf i<n) y xs) i<n ρ ⟩
--         ⅀?⟦ ⊠-Κ-inj (wf i<n) y xs ⟧ (drop-1 i<n   ρ)     ＝⟨ ⊠-Κ-inj-hom (wf i<n) y xs (drop-1 i<n ρ) ⟩
--                         y * ⅀⟦ xs ⟧ (drop-1 i<n   ρ)     ＝⟨ is-abelian-monoid.commutes *-is-abelian-monoid ⟩
--                             ⅀⟦ xs ⟧ (drop-1 i<n   ρ) * y ∎

--       ⊠-⅀-inj-hom : ∀ {i k}
--         → (a : Acc k)
--         → (i<k : i < k)
--         → (xs : Some (Coeff i))
--         → (ys : Poly ⇓ k)
--         → ∀ ρ
--         → ⟦ ⊠-⅀-inj a i<k xs ys ⟧ ρ ＝ ⅀⟦ xs ⟧ (drop-1 i<k ρ) * ⟦ ys ⟧ ρ
--       ⊠-⅀-inj-hom (rek wf) i<k x (Sum ys ⊐ j≤k) = ⊠-match-hom (rek wf) (order i<k j≤k) x ys
--       ⊠-⅀-inj-hom (rek wf) i<k x ([ y ] ⊐ j≤k) ρ =
--           ⟦ ⊠-Κ-inj (wf i<k) y x ⊐↓ i<k ⟧ ρ
--         ＝⟨ ⊐↓-hom (⊠-Κ-inj (wf i<k) y x) i<k ρ ⟩
--           ⅀?⟦ ⊠-Κ-inj (wf i<k) y x ⟧ (drop-1 i<k ρ)
--         ＝⟨ ⊠-Κ-inj-hom (wf i<k) y x (drop-1 i<k ρ) ⟩
--           y * ⅀⟦ x ⟧ (drop-1 i<k ρ)
--         ＝⟨ is-abelian-monoid.commutes *-is-abelian-monoid ⟩
--           ⅀⟦ x ⟧ (drop-1 i<k ρ) * y
--         ∎

--       ⊠-match-hom : ∀ {i j n}
--             → (a : Acc n)
--             → {i<n : i < n}
--             → {j<n : j < n}
--             → (ord : Order i<n j<n)
--             → (xs : Some (Coeff i))
--             → (ys : Some (Coeff j))
--             → (Ρ : Vec A n)
--             → ⟦ ⊠-match a ord xs ys ⟧ Ρ
--             ＝ ⅀⟦ xs ⟧ (drop-1 i<n Ρ) * ⅀⟦ ys ⟧ (drop-1 j<n Ρ)
--       ⊠-match-hom {j = j} (rek wf) (lt i≤j-1 j≤n) xs ys Ρ′ =
--         let (ρ , Ρ) = drop-1 j≤n Ρ′
--             xs′ = ⅀⟦ xs ⟧ (drop-1 (≤-trans (≤-step i≤j-1) j≤n) Ρ′)
--         in
--           ⟦ poly-map ( (⊠-⅀-inj (wf j≤n) i≤j-1 xs)) ys ⊐↓ j≤n ⟧ Ρ′
--         ＝⟨ ⊐↓-hom (poly-map ( (⊠-⅀-inj (wf j≤n) i≤j-1 xs)) ys) j≤n Ρ′ ⟩
--           ⅀?⟦ poly-map ( (⊠-⅀-inj (wf j≤n) i≤j-1 xs)) ys ⟧ (ρ , Ρ)
--         ＝⟨ poly-mapR ρ Ρ (⊠-⅀-inj (wf j≤n) i≤j-1 xs)
--                         (_ *_)
--                         (*-cong refl)
--                         reassoc
--                         (λ _ _ → *-distributes-over-+-right)
--                         (λ y → ⊠-⅀-inj-hom (wf j≤n) i≤j-1 xs y _)
--                         𝟎-absorbs-left ys ⟩
--           ⌜ ⅀⟦ xs ⟧ (drop-1 i≤j-1 Ρ) ⌝ * ⅀⟦ ys ⟧ (ρ , Ρ)
--         ＝⟨ ap! (trans-join-coeffs-hom i≤j-1 j≤n xs Ρ′) ⟩
--           xs′ * ⅀⟦ ys ⟧ (ρ , Ρ)
--         ∎
--       ⊠-match-hom (rek wf) (gt i≤n j≤i-1) xs ys Ρ′ =
--         let (ρ , Ρ) = drop-1 i≤n Ρ′
--             ys′ = ⅀⟦ ys ⟧ (drop-1 (≤-trans (≤-step j≤i-1) i≤n) Ρ′)
--         in
--           ⟦ poly-map ( (⊠-⅀-inj (wf i≤n) j≤i-1 ys)) xs ⊐↓ i≤n ⟧ Ρ′
--         ＝⟨ ⊐↓-hom (poly-map ( (⊠-⅀-inj (wf i≤n) j≤i-1 ys)) xs) i≤n Ρ′ ⟩
--           ⅀?⟦ poly-map ( (⊠-⅀-inj (wf i≤n) j≤i-1 ys)) xs ⟧ (ρ , Ρ)
--         ＝⟨ poly-mapR ρ Ρ (⊠-⅀-inj (wf i≤n) j≤i-1 ys)
--                         (_ *_)
--                         (*-cong refl)
--                         reassoc
--                         (λ _ _ → *-distributes-over-+-right)
--                         (λ x → ⊠-⅀-inj-hom (wf i≤n) j≤i-1 ys x _)
--                         𝟎-absorbs-left xs ⟩
--           ⌜ ⅀⟦ ys ⟧ (drop-1 j≤i-1 Ρ) ⌝ * ⅀⟦ xs ⟧ (ρ , Ρ)
--         ＝⟨ ap! (trans-join-coeffs-hom j≤i-1 i≤n ys Ρ′) ⟩
--           ys′ * ⅀⟦ xs ⟧ (ρ , Ρ)
--         ＝⟨ is-abelian-monoid.commutes *-is-abelian-monoid ⟩
--           ⅀⟦ xs ⟧ (ρ , Ρ) * ys′
--         ∎

--       ⊠-match-hom (rek wf) (eq ij≤n) xs ys Ρ =
--           ⟦ ⊠-coeffs (wf ij≤n) xs ys ⊐↓ ij≤n ⟧ Ρ
--         ＝⟨ ⊐↓-hom (⊠-coeffs (wf ij≤n) xs ys) ij≤n Ρ ⟩
--           ⅀?⟦ ⊠-coeffs (wf ij≤n) xs ys ⟧ (drop-1 ij≤n Ρ)
--         ＝⟨ ⊠-coeffs-hom (wf ij≤n) xs ys (drop-1 ij≤n Ρ) ⟩
--           ⅀⟦ xs ⟧ (drop-1 ij≤n Ρ) * ⅀⟦ ys ⟧ (drop-1 ij≤n Ρ)
--         ∎

--       ⊠-coeffs-hom : ∀ {n}
--           → (a : Acc n)
--           → (xs ys : Some (Coeff n))
--           → ∀ ρ → ⅀?⟦ ⊠-coeffs a xs ys ⟧ ρ ＝ ⅀⟦ xs ⟧ ρ * ⅀⟦ ys ⟧ ρ
--       ⊠-coeffs-hom a xs (y ≢0 Δ j ∷ Nil) (ρ , Ρ) =
--           ⅀?⟦ poly-map (⊠-step′ a y) xs ^* j ⟧ (ρ , Ρ)
--         ＝⟨ sym (pow′-hom j (poly-map (⊠-step′ a y) xs) ρ Ρ) ⟩
--           ⅀?⟦ poly-map (⊠-step′ a y) xs ⟧ (ρ , Ρ) *⟨ ρ ⟩^ j
--         ＝⟨ pow-mul-cong
--               (poly-mapR ρ Ρ
--                 (⊠-step′ a y)
--                 (⟦ y ⟧ Ρ *_)
--                 (*-cong refl)
--                 reassoc
--                 (λ _ _ → *-distributes-over-+-right)
--                 (λ z → ⊠-step′-hom a y z Ρ)
--                 𝟎-absorbs-left
--                 xs)
--               ρ
--               j ⟩
--           (⟦ y ⟧ Ρ * ⅀⟦ xs ⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
--         ＝⟨ pow-opt _ ρ j ⟩
--           (ρ ^ j) * (⟦ y ⟧ Ρ * ⅀⟦ xs ⟧ (ρ , Ρ))
--         ＝⟨ associative *-is-monoid _ _ _ ⟩
--           (ρ ^ j) * ⟦ y ⟧ Ρ * ⅀⟦ xs ⟧ (ρ , Ρ)
--         ＝⟨ is-abelian-monoid.commutes *-is-abelian-monoid ⟩
--           ⅀⟦ xs ⟧ (ρ , Ρ) * ⌜ (ρ ^ j) * ⟦ y ⟧ Ρ ⌝
--         ＝⟨ ap! (sym (pow-opt _ ρ j)) ⟩
--           ⅀⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ *⟨ ρ ⟩^ j)
--         ∎
--       ⊠-coeffs-hom a xs (y ≢0 Δ j ∷ Cons ys) (ρ , Ρ) =
--         let xs′ = ⅀⟦ xs ⟧ (ρ , Ρ)
--             y′  = ⟦ y ⟧ Ρ
--             ys′ = ⅀⟦ ys ⟧ (ρ , Ρ)
--         in
--           ⅀?⟦ para (⊠-cons a y ys) xs ^* j ⟧ (ρ , Ρ)
--         ＝⟨ sym (pow′-hom j (para (⊠-cons a y ys) xs) ρ Ρ) ∙ pow-opt _ ρ j ⟩
--           ρ ^ j * ⌜ ⅀?⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ) ⌝
--         ＝⟨ ap! (⊠-cons-hom a y ys xs ρ Ρ) ⟩
--           ρ ^ j * (xs′ * (ρ * ys′ + y′))
--         ＝⟨ associative *-is-monoid _ _ _ ⟩
--         ⌜ ρ ^ j * xs′ ⌝ * (ρ * ys′ + y′)
--         ＝⟨ ap! (is-abelian-monoid.commutes *-is-abelian-monoid) ⟩
--           (xs′ * ρ ^ j) * (ρ * ys′ + y′)
--         ＝⟨ sym (associative *-is-monoid _ _ _) ⟩
--           xs′ * ⌜ ρ ^ j * (ρ * ys′ + y′) ⌝
--         ＝⟨ ap! (sym (pow-opt _ ρ j)) ⟩
--           xs′ * ((ρ * ys′ + y′) *⟨ ρ ⟩^ j)
--         ∎

--       open Reasoning
--       open import Data.Product.Ext

--       ⊠-cons-hom : ∀ {n}
--         → (a : Acc n)
--         → (y : Poly ⇓ n)
--         → (ys xs : Some (Coeff n))
--         → (ρ : A)
--         → (Ρ : Vec A n)
--         → ⅀?⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ)
--         ＝ ⅀⟦ xs ⟧ (ρ , Ρ) * (ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⟧ Ρ)
--       ⊠-cons-hom a y ys xs ρ Ρ =
--         poly-foldR ρ Ρ
--           (⊠-cons a y ys)
--           (flip _*_ (ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⟧ Ρ))
--           (flip *-cong refl) -- (flip *-cong refl)
--           (λ x y → sym *-assoc)
--           step
--           𝟎-absorbs-right
--           xs
--         where
--         -- step : (y₁ : Poly ⇓ n)
--         --   {ys = ys₁ : Many (PowIndex (NonZero n))} (zs : Many (PowIndex (NonZero n))) →
--         --   ⅀?⟦ ys₁ ⟧ (ρ , Ρ) ＝ ⅀?⟦ zs ⟧ (ρ , Ρ) *
--         --   (ρ * (((NonZero.poly (PowIndex.coeff (hd ys)) , tl ys)
--         --     ⟦∷⟧ (ρ , Ρ))
--         --     *⟨ ρ ⟩^ PowIndex.power (hd ys))
--         --   + ⟦ y ⟧ Ρ) →
--         --   ρ * ⅀?⟦ ⊞-coeffs (para [ ⊠-step a (body y₁) (scope≤n y₁) , id ]ₚ ys) ys₁ ⟧ (ρ , Ρ)
--         --   + ⟦ ⊠-step a (body y₁) (scope≤n y₁) y ⟧ Ρ
--         --   ＝
--         --   (ρ * ⅀?⟦ zs ⟧ (ρ , ?) + ⟦ y₁ ⟧ ?) * (ρ * (((NonZero.poly (PowIndex.coeff (hd ys))
--         --       , tl ys)
--         --     ⟦∷⟧ (ρ , Ρ))
--         --     *⟨ ρ ⟩^ PowIndex.power (hd ys)) + ⟦ y ⟧ Ρ)
--         step = λ { (z ⊐ j≤n) {ys = ys₁} zs ys≋zs →
--           let x′  = ⟦ z ⊐ j≤n ⟧ Ρ
--               xs′ = ⅀?⟦ zs ⟧ (ρ , Ρ)
--               y′  = ⟦ y ⟧ Ρ
--               ys′ = ⅀⟦ ys ⟧ (ρ , Ρ)
--               step = λ y → ⊠-step-hom a z j≤n y Ρ
--           in
--             ρ * ⅀?⟦ ⊞-coeffs (poly-map ( (⊠-step a z j≤n)) ys) ys₁ ⟧ (ρ , Ρ) + ⟦ ⊠-step a z j≤n y ⟧ Ρ
--           ＝⟨ (*≫ ⊞-coeffs-hom (poly-map (⊠-step a z j≤n) ys) _ (ρ , Ρ)) ⟨ +-cong ⟩ ⊠-step-hom a z j≤n y Ρ ⟩
--             ρ * (⅀?⟦ poly-map (⊠-step a z j≤n) ys ⟧ (ρ , Ρ) + ⅀?⟦ ys₁ ⟧ (ρ , Ρ)) + x′ * y′
--           ＝⟨ ≪+ *≫ (poly-mapR ρ Ρ (⊠-step a z j≤n) (x′ *_) (*-cong refl) reassoc (λ _ _ → *-distributes-over-+-right) step 𝟎-absorbs-left ys ⟨ +-cong ⟩ ys≋zs) ⟩
--             ρ * (x′ * ys′ + xs′ * (ρ * ys′ + y′)) + (x′ * y′)
--           ＝⟨ ≪+ *-distributes-over-+-right ⟩
--             ρ * (x′ * ys′) + ρ * (xs′ * (ρ * ys′ + y′)) + (x′ * y′)
--           ＝⟨ (≪+ +-comm) ∙ +-assoc ⟩
--             ρ * (xs′ * (ρ * ys′ + y′)) + (ρ * (x′ * ys′) + (x′ * y′))
--           ＝⟨ sym *-assoc ⟨ +-cong ⟩ ((≪+ (sym *-assoc ∙ (≪* *-comm) ∙ *-assoc)) ∙ sym *-distributes-over-+-right) ⟩
--             ρ * xs′ * (ρ * ys′ + y′) + x′ * (ρ * ys′ + y′)
--           ＝⟨ sym *-distributes-over-+-left ⟩
--             (ρ * xs′ + x′) * (ρ * ys′ + y′)
--           ∎ }

--     ⊠-hom : ∀ {n} (xs ys : Poly ⇓ n) → ∀ ρ → ⟦ xs ⊠ ys ⟧ ρ ＝ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
--     ⊠-hom (xs ⊐ i≤n) = ⊠-step-hom (makeAcc _) xs i≤n
