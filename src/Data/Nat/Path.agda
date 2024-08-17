{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Prelude

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects

open import Data.Nat.Base

private variable m n : ℕ

suc-inj : suc m ＝ suc n → m ＝ n
suc-inj = ap pred

instance
  Reflects-suc : {b : Bool} → ⦃ Reflects (m ＝ n) b ⦄ → Reflects (suc m ＝ suc n) b
  Reflects-suc = Reflects.dmap (ap suc) (contra suc-inj) auto
  {-# INCOHERENT Reflects-suc #-}

  Reflects-ℕ-Path : Reflects (m ＝ n) (m == n)
  Reflects-ℕ-Path {0}     {0}     = ofʸ refl
  Reflects-ℕ-Path {0}     {suc n} = ofⁿ λ p → ¬-so-false $ subst So (ap is-zero? p) oh
  Reflects-ℕ-Path {suc m} {0}     = ofⁿ λ p → ¬-so-false $ subst So (ap is-positive? p) oh
  Reflects-ℕ-Path {suc m} {suc n} =
    Reflects.dmap (ap suc) (λ m≠n sm=sn → false! (m≠n (suc-inj sm=sn))) (Reflects-ℕ-Path {m} {n})

  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete = reflects-path→is-discrete!

ℕ-identity-system : is-identity-system (λ m n → ⌞ m == n ⌟) _
ℕ-identity-system = reflects-path→identity-system!

instance opaque
  H-Level-ℕ : H-Level (2 + n) ℕ
  H-Level-ℕ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 ℕ-identity-system
  {-# OVERLAPPING H-Level-ℕ #-}

-- random stuff
instance
  Reflects-id≠suc : Reflects (m ＝ suc m) false
  Reflects-id≠suc {0}     = Reflects-ℕ-Path
  Reflects-id≠suc {suc m} = Reflects.dmap (ap suc) (contra suc-inj) (Reflects-id≠suc {m})
  {-# INCOHERENT Reflects-id≠suc #-}

  Reflects-suc≠id : Reflects (suc m ＝ m) false
  Reflects-suc≠id = reflects-sym auto
  {-# INCOHERENT Reflects-suc≠id #-}

  Reflects-id≠+-suc : Reflects (n ＝ n + suc m) false
  Reflects-id≠+-suc {0}     = Reflects-ℕ-Path
  Reflects-id≠+-suc {suc n} = Reflects.dmap (ap suc) (contra suc-inj) (Reflects-id≠+-suc {n})
  {-# INCOHERENT Reflects-id≠+-suc #-}

  Reflects-+-suc≠id : Reflects (n + suc m ＝ n) false
  Reflects-+-suc≠id = reflects-sym auto
  {-# INCOHERENT Reflects-+-suc≠id #-}
