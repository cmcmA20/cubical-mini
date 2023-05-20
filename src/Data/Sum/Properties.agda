{-# OPTIONS --safe #-}
module Data.Sum.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Empty.Base

open import Data.Sum.Base

private variable
  a b c d : Level
  A : Type a
  B : Type b
  C : Type c
  D : Type d

⊎-universal : {C : A ⊎ B → Type c}
            → (Π[ x ꞉ A ⊎ B ] C x)
            ≃ ( (Π[ x ꞉ A ] C (inj-l x))
              × (Π[ y ꞉ B ] C (inj-r y))
              )
⊎-universal = Iso→Equiv the-iso where
  the-iso : Iso _ _
  the-iso .fst f = (λ x → f (inj-l x)) , (λ x → f (inj-r x))
  the-iso .snd .is-iso.inv (f , g) (inj-l x) = f x
  the-iso .snd .is-iso.inv (f , g) (inj-r x) = g x
  the-iso .snd .is-iso.rinv x = refl
  the-iso .snd .is-iso.linv f i (inj-l x) = f (inj-l x)
  the-iso .snd .is-iso.linv f i (inj-r x) = f (inj-r x)

⊎-ap : A ≃ B → C ≃ D → (A ⊎ C) ≃ (B ⊎ D)
⊎-ap (f , f-eqv) (g , g-eqv) = Iso→Equiv cong′ where
  f-iso = is-equiv→is-iso f-eqv
  g-iso = is-equiv→is-iso g-eqv

  cong′ : Iso _ _
  cong′ .fst = map f g
  cong′ .snd .is-iso.inv  (inj-l x) = inj-l (f-iso .is-iso.inv x)
  cong′ .snd .is-iso.inv  (inj-r x) = inj-r (g-iso .is-iso.inv x)
  cong′ .snd .is-iso.rinv (inj-l x) = ap inj-l (f-iso .is-iso.rinv x)
  cong′ .snd .is-iso.rinv (inj-r x) = ap inj-r (g-iso .is-iso.rinv x)
  cong′ .snd .is-iso.linv (inj-l x) = ap inj-l (f-iso .is-iso.linv x)
  cong′ .snd .is-iso.linv (inj-r x) = ap inj-r (g-iso .is-iso.linv x)

⊎-ap-l : A ≃ B → (A ⊎ C) ≃ (B ⊎ C)
⊎-ap-l f = ⊎-ap f idₑ

⊎-ap-r : B ≃ C → (A ⊎ B) ≃ (A ⊎ C)
⊎-ap-r f = ⊎-ap idₑ f

⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = Iso→Equiv i where
  i : Iso _ _
  i .fst (inj-l x) = inj-r x
  i .fst (inj-r x) = inj-l x

  i .snd .is-iso.inv (inj-l x) = inj-r x
  i .snd .is-iso.inv (inj-r x) = inj-l x

  i .snd .is-iso.rinv (inj-l x) = refl
  i .snd .is-iso.rinv (inj-r x) = refl
  i .snd .is-iso.linv (inj-l x) = refl
  i .snd .is-iso.linv (inj-r x) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = Iso→Equiv i where
  i : Iso _ _
  i .fst (inj-l (inj-l x)) = inj-l x
  i .fst (inj-l (inj-r x)) = inj-r (inj-l x)
  i .fst (inj-r x)       = inj-r (inj-r x)

  i .snd .is-iso.inv (inj-l x)       = inj-l (inj-l x)
  i .snd .is-iso.inv (inj-r (inj-l x)) = inj-l (inj-r x)
  i .snd .is-iso.inv (inj-r (inj-r x)) = inj-r x

  i .snd .is-iso.rinv (inj-l x) = refl
  i .snd .is-iso.rinv (inj-r (inj-l x)) = refl
  i .snd .is-iso.rinv (inj-r (inj-r x)) = refl

  i .snd .is-iso.linv (inj-l (inj-l x)) = refl
  i .snd .is-iso.linv (inj-l (inj-r x)) = refl
  i .snd .is-iso.linv (inj-r x) = refl

⊎-zero-r : (A ⊎ ⊥) ≃ A
⊎-zero-r .fst (inj-l x) = x
⊎-zero-r .snd .equiv-proof y .fst = inj-l y , refl
⊎-zero-r .snd .equiv-proof y .snd (inj-l x , p) i = inj-l (p (~ i)) , λ j → p (~ i ∨ j)

⊎-zero-l : (⊥ ⊎ A) ≃ A
⊎-zero-l .fst (inj-r x) = x
⊎-zero-l .snd .equiv-proof y .fst = inj-r y , refl
⊎-zero-l .snd .equiv-proof y .snd (inj-r x , p) i = inj-r (p (~ i)) , λ j → p (~ i ∨ j)

⊎-×-distribute : ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
⊎-×-distribute = Iso→Equiv i where
  i : Iso _ _
  i .fst (inj-l x , y) = inj-l (x , y)
  i .fst (inj-r x , y) = inj-r (x , y)
  i .snd .is-iso.inv (inj-l (x , y)) = inj-l x , y
  i .snd .is-iso.inv (inj-r (x , y)) = inj-r x , y
  i .snd .is-iso.rinv (inj-l x) = refl
  i .snd .is-iso.rinv (inj-r x) = refl
  i .snd .is-iso.linv (inj-l x , _) = refl
  i .snd .is-iso.linv (inj-r x , _) = refl
