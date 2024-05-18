{-# OPTIONS --safe #-}
module Combinatorics.Finiteness.Listed.Strong where

open import Meta.Prelude

open import Meta.Marker
open import Meta.Membership
open import Meta.Record

open import Logic.Discreteness

open import Combinatorics.Finiteness.Bishop.Manifest

open import Functions.Embedding

open import Data.Dec.Base
open import Data.Empty.Base as ⊥
open import Data.Dec.Properties
open import Data.Fin.Computational.Base as Fin
open import Data.Fin.Computational.Instances.Discrete
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Membership
open import Data.List.Path

record Listed {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  constructor finiteₗ
  field
    support : List A
    cover   : Π[ x ꞉ A ] x ∈! support

open Listed public

unquoteDecl Listed-iso = declare-record-iso Listed-iso (quote Listed)

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ
  n : HLevel

instance
  H-Level-Listed : ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level n A ⦄ → H-Level n (Listed A)
  H-Level-Listed {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = ≅→is-of-hlevel n Listed-iso (hlevel n)

listed→Σ∈!-is-discrete : (lis : Listed A) → is-discrete (Σ[ x ꞉ A ] x ∈! lis .support)
listed→Σ∈!-is-discrete lis {a₁ , a₁∈l , u} {a₂ , a₂∈l , v} = caseᵈ ∈ₗ→fin a₁∈l ＝ ∈ₗ→fin a₂∈l of λ where
  (yes p=q) → yes (∈ₗ→fin-almost-injective a₁∈l a₂∈l p=q ,ₚ prop!)
  (no  p≠q) → no λ x → p≠q (∈ₗ→fin-respects-∈!ₗ a₁∈l u a₂∈l v (ap fst x))

listed-embedding : (lis : Listed A) → A ↪ (Σ[ x ꞉ A ] x ∈! lis .support)
listed-embedding lis .fst a = a , lis .cover a
listed-embedding lis .snd (c , c∈l , u) (a , p) (b , q)
  =  ap fst (p ∙ q ⁻¹)
  ,ₚ Σ-prop-square! (commutes→square lemma)
  where
  lemma : ap fst (p ∙ q ⁻¹) ∙ ap fst q ＝ ap fst p ∙ refl
  lemma =
    ⌜ ap fst (p ∙ q ⁻¹) ⌝ ∙ ap fst q       ~⟨ ap! (ap-comp-∙ fst p _) ⟩
    (ap fst p ∙ ap fst (q ⁻¹)) ∙ ap fst q  ~⟨ ∙-cancel-r _ _ ⟩
    ap fst p                               ~⟨ ∙-id-r _ ⟨
    ap fst p ∙ refl                        ∎

listability↪fin
  : (lis : Listed A)
  → (Σ[ a ꞉ A ] a ∈! lis .support) ↪ Fin (length (lis .support))
listability↪fin lis .fst (a , a∈l , u) = ∈ₗ→fin a∈l
listability↪fin lis .snd _ ((_ , (b , _)) , y) ((_ , (c , _)) , z) =
  (∈ₗ→fin-almost-injective b c (y ∙ z ⁻¹) ,ₚ prop!) ,ₚ prop!

listed→is-discrete : Listed A → is-discrete A
listed→is-discrete lis = ↪→is-discrete (listed-embedding lis) (listed→Σ∈!-is-discrete lis)

lookup-safe : {xs : List A} → Fin (length xs) → A
lookup-safe {xs = x ∷ xs} (mk-fin 0) = x
lookup-safe {xs = x ∷ xs} (mk-fin (suc index) {(z)}) = lookup-safe {xs = xs} (mk-fin index {z})

-- poo
--   : {A : Type ℓᵃ}
--     {xs : List A} {cov : Π[ x ꞉ A ] x ∈! xs}
--   → loo is-right-inverse-of (λ x → ∈ₗ→fin (cov x .fst))
-- poo {xs = x ∷ xs} {cov} (mk-fin 0) with cov x
-- ... | here  _ , _ = refl
-- ... | there p , u = ⊥.rec (there≠here $ u (here refl))
-- poo {xs = x ∷ xs} {cov} (mk-fin (suc index) {(z)}) =
--   let zz = poo {xs = xs} {λ a → let uq = cov a in {!!} , {!!}} (mk-fin index {z})
--   in {!!} ∙ ap fsuc zz

shto
  : {A : Type ℓᵃ} (lis : Listed A)
  → Σ[ a ꞉ A ] a ∈! lis .support ≃ A
shto lis = ≅→≃ $ fst , iso < id , lis .cover > (λ _ → refl) λ (_ , _) → refl ,ₚ prop!

-- sheesha
--   : {A : Type ℓᵃ} (lis : Listed A)
--   → Σ[ a ꞉ A ] a ∈! lis .support
--   ≃ Σ[ a ꞉ A ] Σ[ k ꞉ Fin (length (lis .support)) ] (lookup-safe k ＝ a)
-- sheesha lis = Σ-ap-snd {!!}

poosha
  : {A : Type ℓᵃ} (lis : Listed A)
  → (Σ[ a ꞉ A ] a ∈! lis .support)
  ≃ (Fin (length (lis .support)))
poosha {A} lis =
  Σ[ a ꞉ A ] a ∈! lis .support                                          ~⟨ Σ-ap-snd (λ a → {!!}) ⟩
  Σ[ a ꞉ A ] Σ[ k ꞉ Fin (length (lis .support)) ] (lookup-safe k ＝ a)  ~⟨ Σ-swap ⟩
  Σ[ k ꞉ Fin (length (lis .support)) ] Σ[ a ꞉ A ] (lookup-safe k ＝ a)  ~⟨ Σ-contract-snd (λ k → singletonₚ-is-contr (lookup-safe k , refl)) ⟩
  Fin (length (lis .support))                                           ∎

open import Data.Vec.Inductive

bebenya
  : {A : Type ℓᵃ} {n : ℕ}
  → Σ[ support ꞉ Vec A n ] Π[ x ꞉ A ] x ∈! support
  ≃ (A ≃ Fin n)
bebenya = ≅→≃ (to , {!!}) where
  to : Σ[ support ꞉ Vec A n ] Π[ x ꞉ A ] x ∈! support → A ≃ Fin n
  to (xs , f) .fst a = let (k , p) , u = f a in {!!}
  to (xs , f) .snd .equiv-proof k = {!!}

listed≃manifest-bishop-finite : Listed A ≃ Manifest-bishop-finite A
listed≃manifest-bishop-finite {A} =
  Listed A                                                         ~⟨ ≅→≃ Listed-iso ⟩
  Σ[ support ꞉ List A ] Π[ x ꞉ A ] x ∈! support                    ~⟨ Σ-ap list≃vec (λ xs → Π-cod-≃ λ a → {!!}) ⟩
  Σ[ (n , support) ꞉ Σ[ n ꞉ ℕ ] Vec A n ] Π[ x ꞉ A ] x ∈! support  ~⟨ Σ-assoc ⟨
  Σ[ n ꞉ ℕ ] Σ[ support ꞉ Vec A n ] Π[ x ꞉ A ] x ∈! support        ~⟨ Σ-ap-snd (λ n → bebenya) ⟩
  Σ[ n ꞉ ℕ ] (A ≃ Fin n)                                           ~⟨ ≅→≃ manifest-bishop-finite-iso ⟨
  Manifest-bishop-finite A                                         ∎
