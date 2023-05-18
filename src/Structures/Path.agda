{-# OPTIONS --safe #-}
module Structures.Path where

open import Foundations.Base
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ : Level
  S : Type ℓ → Type ℓ′

_on-paths-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-paths-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

-- observe that "being a proposition" is a pointed structure on paths
_ : id on-paths-of_ ＝ is-prop {ℓ}
_ = fun-ext (λ _ → refl)

-- TODO is it even needed?
-- The general version is provable only in erased context
-- Are there any non-univalent structures on paths?
@0 Path-str : Structure ℓ′ S → Structure _ (λ X → S on-paths-of X)
Path-str σ .is-hom (A , f) (B , g) h = let open Equiv h in
  Π[ a ꞉ A ] Π[ a′ ꞉ A ] σ .is-hom
    ((a ＝ a′) , f a a′)
    ((to a ＝ to a′) , g (to a) (to a′))
    (ap to , ap-is-equiv _ (h .snd))

-- Path-str2 : Structure ℓ′ S → Structure _ (λ X → S on-paths-of X)
-- Path-str2 σ .is-hom (A , f) (B , g) h = let open Equiv h in
--   Π[ a ꞉ A ] Π[ b ꞉ B ] σ .is-hom
--     ((   a ＝ from b) , f     a (from b))
--     ((to a ＝      b) , g (to a)      b)
--     ((λ r → ap to r ∙ ε _) , record { equiv-proof = λ s → (sym (η _) ∙ ap from s , {!!}) , {!!} })

-- @0 Path-str-is-univalent : {σ : Structure ℓ′ S} → is-univalent σ → is-univalent (Path-str σ)
-- Path-str-is-univalent {S} {σ} is-univ {A , f} {B , g} e =
--   (Π[ a ꞉ A ] Π[ a′ ꞉ A ] σ .is-hom _ _ _)     ≃⟨ {!!} ⟩
--   {!!}                                         ≃⟨ (hetero-homotopy≃homotopy ₑ⁻¹) ∙ₑ funext-dep-≃ ⟩
--   ＜ f ／ (λ i → S on-paths-of ua e i) ＼ g ＞ ≃∎
