{-# OPTIONS --safe #-}
module Functions.Equiv.Biinv where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Foundations.Isomorphism

private variable
  ℓ : Level
  A B C : Type ℓ
  f : A → B

linv : (A → B) → Type _
linv f = Σ[ g ꞉ (_ → _) ] (g ∘ f ＝ id)

rinv : (A → B) → Type _
rinv f = Σ[ h ꞉ (_ → _) ] (f ∘ h ＝ id)

is-biinv : (A → B) → Type _
is-biinv f = linv f × rinv f

is-iso→is-contr-linv : is-iso f → is-contr (linv f)
is-iso→is-contr-linv isiso =
  is-equiv→post-is-equiv (is-iso→is-equiv isiso) .equiv-proof id

is-iso→is-contr-rinv : is-iso f → is-contr (rinv f)
is-iso→is-contr-rinv isiso =
  is-equiv→pre-is-equiv (is-iso→is-equiv isiso) .equiv-proof id

_ : {f : A → B} → linv f ＝ fibre (_∘ f) id
_ = refl

_ : {f : A → B} → rinv f ＝ fibre (f ∘_) id
_ = refl

is-biinv→is-iso : is-biinv f → is-iso f
is-biinv→is-iso {f} ((g , g∘f=id) , h , h∘f=id) = iso h (happly h∘f=id) β
  where
    β : (x : _) → h (f x) ＝ x
    β x =
      h (f x)         ~⟨ happly g∘f=id _ ⟨
      g (f (h (f x))) ~⟨ ap g (happly h∘f=id _) ⟩
      g (f x)         ~⟨ happly g∘f=id _ ⟩
      x               ∎

is-biinv-is-prop : is-prop (is-biinv f)
is-biinv-is-prop {f} = contractible-if-inhabited contract where
  contract : is-biinv f → is-contr (is-biinv f)
  contract ibiinv =
    ×-is-of-hlevel 0 (is-iso→is-contr-linv iiso)
                     (is-iso→is-contr-rinv iiso)
    where iiso = is-biinv→is-iso ibiinv

is-iso→is-biinv : is-iso f → is-biinv f
is-iso→is-biinv iiso .fst = iiso .is-iso.inv , fun-ext (iiso .is-iso.linv)
is-iso→is-biinv iiso .snd = iiso .is-iso.inv , fun-ext (iiso .is-iso.rinv)
