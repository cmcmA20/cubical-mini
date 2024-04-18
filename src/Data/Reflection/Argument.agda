{-# OPTIONS --safe #-}
module Data.Reflection.Argument where

open import Foundations.Base

open import Data.List.Base

open import Agda.Builtin.Reflection
  public
  using ( Visibility ; visible ; hidden ; instance′
        ; Relevance ; relevant ; irrelevant
        ; Quantity ; quantity-0 ; quantity-ω
        ; Modality ; modality
        ; arg-info
        ; Arg ; arg
        )
  renaming ( ArgInfo to Arg-info )

pattern default-modality = modality relevant quantity-ω

modality→relevance : Modality → Relevance
modality→relevance (modality r _) = r

modality→quantity : Modality → Quantity
modality→quantity (modality _ q) = q

pattern default-modality = modality relevant quantity-ω
pattern erased-modality = modality relevant quantity-0
pattern irrelevant-modality = modality irrelevant quantity-ω
pattern irrelevant-erased-modality = modality irrelevant quantity-0


arg-vis : Arg-info → Visibility
arg-vis (arg-info v _) = v

arg-modality : Arg-info → Modality
arg-modality (arg-info _ m) = m

pattern default-ai = arg-info visible default-modality

private variable
  ℓ : Level
  A : Type ℓ

unai : Arg A → Arg-info
unai (arg i _) = i

unarg : Arg A → A
unarg (arg _ x) = x

pattern vis-arg v t = arg (arg-info v default-modality) t

pattern varg t = vis-arg visible t
pattern harg t = vis-arg hidden t
pattern iarg t = vis-arg instance′ t

pattern _v∷_ t xs = varg t ∷ xs
pattern _h∷_ t xs = harg t ∷ xs
pattern _hm∷_ t xs = arg (arg-info hidden (modality relevant _)) t ∷ xs
pattern _i∷_ t xs = iarg t ∷ xs

infixr 30 _v∷_ _h∷_ _hm∷_ _i∷_

argH0 argH argI argN : A → Arg A
argH  = arg (arg-info hidden default-modality)
argI  = arg (arg-info instance′ default-modality)
argH0 = arg (arg-info hidden erased-modality)
argN  = vis-arg visible
