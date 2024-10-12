{-# OPTIONS --safe #-}
module Functions.Equiv.Biinv where

open import Foundations.Prelude

open import Meta.Record

private variable
  ℓ : Level
  A B C : Type ℓ
  f : A → B

is-biinv : (A → B) → Type _
is-biinv f = has-retraction f × has-section f

qinv→is-contr-retraction
  : {f : A → B}
  → quasi-inverse f → is-contr (has-retraction f)
qinv→is-contr-retraction i = ≅→is-of-hlevel 0 has-retraction-Iso $
  is-equiv→post-is-equiv (qinv→is-equiv i) .equiv-proof id

qinv→is-contr-section
  : {f : A → B}
  → quasi-inverse f → is-contr (has-section f)
qinv→is-contr-section i = ≅→is-of-hlevel 0 has-section-Iso $
  is-equiv→pre-is-equiv (qinv→is-equiv i) .equiv-proof id

is-biinv→qinv
  : {f : A → B}
  → is-biinv f → quasi-inverse f
is-biinv→qinv {f} (hr , hs) = qinv g (hs .is-section) (fun-ext β) where
  g = hs .section
  h = hr .retraction
  β : ∀ x → hs .section (f x) ＝ x
  β x =
    g (f x)          ~⟨ hr .is-retraction # g (f x) ⟨
    h (f (g (f x)))  ~⟨ ap h (hs .is-section # f x) ⟩
    h (f x)          ~⟨ hr .is-retraction # x ⟩
    x                ∎

is-biinv-is-prop : is-prop (is-biinv f)
is-biinv-is-prop {f} = contractible-if-inhabited contract where
  contract : is-biinv f → is-contr (is-biinv f)
  contract ibiinv =
    ×-is-of-hlevel 0 (qinv→is-contr-retraction i)
                     (qinv→is-contr-section i)
    where i = is-biinv→qinv ibiinv

qinv→is-biinv : {f : A → B} → quasi-inverse f → is-biinv f
qinv→is-biinv iiso .fst .retraction = iiso .quasi-inverse.inv
qinv→is-biinv iiso .fst .is-retraction =
  iiso .quasi-inverse.inverses .Inverses.inv-i
qinv→is-biinv iiso .snd .section = iiso .quasi-inverse.inv
qinv→is-biinv iiso .snd .is-section =
  iiso .quasi-inverse.inverses .Inverses.inv-o
