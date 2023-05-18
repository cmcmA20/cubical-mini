{-# OPTIONS --safe #-}
module Data.Sum.Base where

open import Foundations.Base
open import Foundations.Equiv

infixr 1 _⊎_
data _⊎_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  inj-l : A → A ⊎ B
  inj-r : B → A ⊎ B

private variable
  a b c d : Level
  A : Type a
  B : Type b
  C : Type c
  D : Type d

[_,_]ᵤ : (A → C) → (B → C) → (A ⊎ B) → C
[ f , _ ]ᵤ (inj-l x) = f x
[ _ , g ]ᵤ (inj-r x) = g x

[]-unique
  : ∀ {f : A → C} {g : B → C} {h}
  → f ＝ h ∘ inj-l
  → g ＝ h ∘ inj-r
  → [ f , g ]ᵤ ＝ h
[]-unique p q = fun-ext λ { (inj-l x) i → p i x ; (inj-r x) i → q i x }

[]-η : (x : A ⊎ B) → [ inj-l , inj-r ]ᵤ x ＝ x
[]-η (inj-l x) = refl
[]-η (inj-r x) = refl

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

map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g (inj-l a) = inj-l (f a)
map f g (inj-r b) = inj-r (g b)

map-l : (A → C) → A ⊎ B → C ⊎ B
map-l f = map f id

map-r : (B → C) → A ⊎ B → A ⊎ C
map-r f = map id f

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
