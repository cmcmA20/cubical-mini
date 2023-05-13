{-# OPTIONS --safe #-}
module Data.Float.Internal where

open import Agda.Builtin.Float public
  using ( Float )
  renaming
    ( -- Relations
      primFloatInequality     to float-inequality       -- Float → Float → Bool
    ; primFloatEquality       to float-equality         -- Float → Float → Bool
    ; primFloatLess           to float-less             -- Float → Float → Bool
    ; primFloatIsInfinite     to float-is-infinite      -- Float → Bool
    ; primFloatIsNaN          to float-is-NaN           -- Float → Bool
    ; primFloatIsNegativeZero to float-is-negative-zero -- Float → Bool
    ; primFloatIsSafeInteger  to float-is-safe-integer  -- Float → Bool
      -- Conversions
    ; primFloatToWord64 to float-to-word64 -- Float → Maybe Word64
    ; primNatToFloat    to ℕ-to-float      -- ℕ → Float
    ; primIntToFloat    to ℤ-to-float      -- ℤ → Float
    ; primFloatRound    to float-round     -- Float → Maybe ℤ
    ; primFloatFloor    to float-floor     -- Float → Maybe ℤ
    ; primFloatCeiling  to float-ceil      -- Float → Maybe ℤ
    ; primFloatToRatio  to float-to-ratio  -- Float → Int × Int
    ; primRatioToFloat  to ratio-to-float  -- ℤ → ℤ → Float
    ; primFloatDecode   to float-decode    -- Float → Maybe (ℤ × ℤ)
    ; primFloatEncode   to float-encode    -- ℤ → ℤ → Maybe Float
    ; primShowFloat     to show-float      -- Float → String
      -- Operations
    ; primFloatPlus   to float-plus   -- Float → Float → Float
    ; primFloatMinus  to float-minus  -- Float → Float → Float
    ; primFloatTimes  to float-times  -- Float → Float → Float
    ; primFloatDiv    to float-div    -- Float → Float → Float
    ; primFloatPow    to float-pow    -- Float → Float → Float
    ; primFloatNegate to float-negate -- Float → Float
    ; primFloatSqrt   to float-sqrt   -- Float → Float
    ; primFloatExp    to float-exp    -- Float → Float
    ; primFloatLog    to float-log    -- Float → Float
    ; primFloatSin    to float-sin    -- Float → Float
    ; primFloatCos    to float-cos    -- Float → Float
    ; primFloatTan    to float-tan    -- Float → Float
    ; primFloatASin   to float-asin   -- Float → Float
    ; primFloatACos   to float-acos   -- Float → Float
    ; primFloatATan   to float-atan   -- Float → Float
    ; primFloatATan2  to float-atan2  -- Float → Float → Float
    ; primFloatSinh   to float-sinh   -- Float → Float
    ; primFloatCosh   to float-cosh   -- Float → Float
    ; primFloatTanh   to float-tanh   -- Float → Float
    ; primFloatASinh  to float-asinh  -- Float → Float
    ; primFloatACosh  to float-acosh  -- Float → Float
    ; primFloatATanh  to float-atanh  -- Float → Float
    )
