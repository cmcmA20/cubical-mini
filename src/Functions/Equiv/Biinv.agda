{-# OPTIONS --safe #-}
module Functions.Equiv.Biinv where

open import Foundations.Prelude

open import Meta.Record

private variable
  ℓ : Level
  A B C : Type ℓ
  f : A → B

is-biinv : (A → B) → Type _
is-biinv f = has-retract f × has-section f

is-inv→is-contr-retract
  : {f : A → B}
  → is-invertible f → is-contr (has-retract f)
is-inv→is-contr-retract i = ≅→is-of-hlevel 0 has-retract-Iso $
  is-equiv→post-is-equiv (is-inv→is-equiv i) .equiv-proof id

is-inv→is-contr-section
  : {f : A → B}
  → is-invertible f → is-contr (has-section f)
is-inv→is-contr-section i = ≅→is-of-hlevel 0 has-section-Iso $
  is-equiv→pre-is-equiv (is-inv→is-equiv i) .equiv-proof id

is-biinv→is-inv
  : {f : A → B}
  → is-biinv f → is-invertible f
is-biinv→is-inv {f} (hr , hs) = invertible g (hs .is-section) (fun-ext β) where
  g = hs .section
  h = hr .retract
  β : ∀ x → hs .section (f x) ＝ x
  β x =
    g (f x)          ~⟨ hr .is-retract # g (f x) ⟨
    h (f (g (f x)))  ~⟨ ap h (hs .is-section # f x) ⟩
    h (f x)          ~⟨ hr .is-retract # x ⟩
    x                ∎

is-biinv-is-prop : is-prop (is-biinv f)
is-biinv-is-prop {f} = contractible-if-inhabited contract where
  contract : is-biinv f → is-contr (is-biinv f)
  contract ibiinv =
    ×-is-of-hlevel 0 (is-inv→is-contr-retract i)
                     (is-inv→is-contr-section i)
    where i = is-biinv→is-inv ibiinv

is-inv→is-biinv : {f : A → B} → is-invertible f → is-biinv f
is-inv→is-biinv iiso .fst .retract = iiso .is-invertible.inv
is-inv→is-biinv iiso .fst .is-retract =
  iiso .is-invertible.inverses .Inverses.inv-i
is-inv→is-biinv iiso .snd .section = iiso .is-invertible.inv
is-inv→is-biinv iiso .snd .is-section =
  iiso .is-invertible.inverses .Inverses.inv-o
