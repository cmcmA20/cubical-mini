{-# OPTIONS --safe #-}
open import Algebra.Monoid.Category
module Algebra.Monoid.Cayley {ℓ} (M : Monoid ℓ) where

open import Algebra.Monoid
open import Categories.Prelude
open import Categories.Displayed.Total
open import Categories.Displayed.Univalence.Thin
open Monoid-on (M .snd)
open Monoid-hom

M′ : Monoid ℓ
M′ = Endo (M .fst)

-- first stage, inject into raw endomorphism monoid
injᵣ : M →̇ (M →̇ M)
injᵣ x = x ⋆_

injᵣ-hom : Monoids.Hom M M′
injᵣ-hom .Total-hom.hom = injᵣ
injᵣ-hom .Total-hom.preserves .pres-id = ext id-l
injᵣ-hom .Total-hom.preserves .pres-⋆ _ _ = ext λ _ → sym $ assoc _ _ _

injᵣ-injective : Injective injᵣ
injᵣ-injective {x} {y} p =
  x       ＝˘⟨ id-r _ ⟩
  x ⋆ id  ＝⟨ p #ₚ _ ⟩
  y ⋆ id  ＝⟨ id-r _ ⟩
  y       ∎

is-representable : M′ →̇ Type ℓ
is-representable f = ∀ x g h → x ＝ g ⋆ h → f x ＝ f g ⋆ h

⌞Cayley⌟ : Set ℓ
⌞Cayley⌟ = el! (Σ[ f ꞉ M′ ] is-representable f)

-- submonoid of endos
Cayley : Monoid ℓ
Cayley .fst = ⌞Cayley⌟
Cayley .snd .Monoid-on.id = idₜ , λ _ _ _ → idₜ
Cayley .snd .Monoid-on._⋆_ (f , fr) (g , gr) = f ∘′ g , λ x u v p → fr (g x) (g u) v (gr x u v p)
Cayley .snd .Monoid-on.has-monoid = to-is-monoid go where
  open make-monoid
  go : make-monoid _
  go .monoid-is-set = hlevel!
  go .id = _
  go ._⋆_ = _
  go .id-l _ = refl
  go .id-r _ = refl
  go .assoc _ _ _ = refl

injᵣ-is-repr : Π[ x ꞉ M ] is-representable (injᵣ x)
injᵣ-is-repr x y g h p =
  x ⋆ ⌜ y ⌝    ＝⟨ ap! p ⟩
  x ⋆ g ⋆ h    ＝⟨ assoc _ _ _ ⟩
  (x ⋆ g) ⋆ h  ∎

inj : M →̇ Cayley
inj = < injᵣ , injᵣ-is-repr >

inj-hom : Monoids.Hom M Cayley
inj-hom .Total-hom.hom = inj
inj-hom .Total-hom.preserves .pres-id =
  injᵣ-hom .Total-hom.preserves .pres-id ,ₚ prop!
inj-hom .Total-hom.preserves .pres-⋆ _ _ =
  injᵣ-hom .Total-hom.preserves .pres-⋆ _ _ ,ₚ prop!

proj : (f : ⌞ Cayley ⌟) → Σ[ g ꞉ M ] (injᵣ g ＝ f .fst)
proj (f , fr) = f id , ext λ x → sym (fr x id x (sym (id-l _)))

lol : Iso ⌞ M ⌟ ⌞ Cayley ⌟
lol .fst = inj
lol .snd .is-iso.inv = fst ∘ₜ proj
lol .snd .is-iso.rinv f = proj f .snd ,ₚ prop!
lol .snd .is-iso.linv = id-r

byak : Erased (M ＝ Cayley)
byak = ∫-Path Monoids-equational inj-hom (is-iso→is-equiv (lol .snd))

strictify : ∀ {ℓ′} (P : Monoid ℓ → 𝒰 ℓ′) → Erased (P Cayley) → Erased (P M)
strictify P q .erased = transport (ap P (sym (byak .erased))) (q .erased)

solve′ : {x y : ⌞ M ⌟} → inj x ＝ inj y → x ＝ y
solve′ p = sym (id-r _) ∙ (ap fst p #ₚ id) ∙ id-r _

solve : {x y : ⌞ M ⌟} → injᵣ x ＝ injᵣ y → x ＝ y
solve = injᵣ-injective
