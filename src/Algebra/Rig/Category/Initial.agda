{-# OPTIONS --safe #-}
module Algebra.Rig.Category.Initial where

open import Algebra.Rig
open import Algebra.Rig.Category.Base

open import Categories.Diagram.Initial
open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude

open import Data.Nat as ℕ

private variable ℓ : Level

Initial-rig : Initial (Rigs ℓ)
Initial-rig = mk-initial ℕᵣ ℕ-is-initial where
  ℕᵣ : Rig ℓ
  ℕᵣ = el! (Lift _ ℕ) , to-rig-on go where
    go : make-rig _
    go .make-rig.rig-is-set = hlevel!
    go .make-rig.0a = lift 0
    go .make-rig.1a = lift 1
    go .make-rig._+_ (lift m) (lift n) = lift (m + n)
    go .make-rig._·_ (lift m) (lift n) = lift (m · n)
    go .make-rig.+-id-l _ = refl
    go .make-rig.+-id-r (lift m) = ap lift (+-zero-r m)
    go .make-rig.+-assoc (lift m) (lift n) (lift k) = ap lift (+-assoc m n k)
    go .make-rig.+-comm (lift m) (lift n) = ap lift (+-comm n m)
    go .make-rig.·-id-l (lift m) = ap lift (·-id-l m)
    go .make-rig.·-id-r (lift m) = ap lift (·-id-r m)
    go .make-rig.·-assoc (lift m) (lift n) (lift k) = ap lift (·-assoc m n k)
    go .make-rig.·-distrib-+-l (lift m) (lift n) (lift k) = ap lift (·-distrib-+-l m n k)
    go .make-rig.·-distrib-+-r (lift m) (lift n) (lift k) = ap lift (·-distrib-+-r n k m)
    go .make-rig.·-absorb-l _ = refl
    go .make-rig.·-absorb-r (lift m) = ap lift (·-absorb-r m)

  ℕ-is-initial : is-initial (Rigs ℓ) ℕᵣ
  ℕ-is-initial {ℓ} R = ℕ→R , λ x → ext $ uniq x where
    module R = Rig-on (R .snd)

    f : ℕ →̇ R
    f 0             = R.0a
    f 1             = R.1a
    f (suc (suc n)) = R.1a R.+ f (suc n)

    f-suc  : ∀ n → f (suc n) ＝ R.1a R.+ f n
    f-suc 0       = sym (R.+-id-r _)
    f-suc (suc _) = refl

    f-plus : ∀ m n → f (m + n) ＝ f m R.+ f n
    f-plus 0       _ = sym (R.+-id-l _)
    f-plus (suc m) n =
      f (suc m + n)             ~⟨ f-suc (m + n) ⟩
      R.1a R.+ ⌜ f (m + n) ⌝    ~⟨ ap! (f-plus m n) ⟩
      R.1a R.+ f m R.+ f n      ~⟨ R.+-assoc _ _ _ ⟩
      ⌜ R.1a R.+ f m ⌝ R.+ f n  ~⟨ ap¡ (f-suc m) ⟨
      f (suc m) R.+ f n         ∎

    f-mul : ∀ m n → f (m · n) ＝ f m R.· f n
    f-mul 0       _ = sym (R.·-absorb-l _)
    f-mul (suc m) n =
      f (n + m · n)                ~⟨ f-plus n (m · n) ⟩
      f n R.+ ⌜ f (m · n) ⌝        ~⟨ ap! (f-mul m n) ⟩
      ⌜ f n ⌝ R.+ f m R.· f n      ~⟨ ap¡ (R.·-id-l _) ⟨
      f 1 R.· f n R.+ f m R.· f n  ~⟨ R.·-distrib-+-r (f n) _ _ ⟨
      ⌜ f 1 R.+ f m ⌝ R.· f n      ~⟨ ap¡ (f-suc m) ⟨
      f (suc m) R.· f n            ∎

    ℕ→R : Rigs.Hom ℕᵣ R
    ℕ→R .hom (lift m) = f m
    ℕ→R .preserves .Semiring-hom.pres-0 = refl
    ℕ→R .preserves .Semiring-hom.pres-1 = refl
    ℕ→R .preserves .Semiring-hom.pres-+ (lift m) (lift n) = f-plus m n
    ℕ→R .preserves .Semiring-hom.pres-· (lift m) (lift n) = f-mul m n

    uniq : (g : Rigs.Hom ℕᵣ R) (m : ℕ) → ℕ→R # lift m ＝ g # lift m
    uniq g 0       = sym (g .preserves .Semiring-hom.pres-0)
    uniq g (suc m) =
      f (suc m)                            ~⟨ f-suc m ⟩
      R.1a R.+ ⌜ f m ⌝                     ~⟨ ap! (uniq g m) ⟩
      ⌜ R.1a ⌝ R.+ g .hom (lift m)         ~⟨ ap¡ (g .preserves .Semiring-hom.pres-1) ⟨
      g .hom (lift 1) R.+ g .hom (lift m)  ~⟨ g .preserves .Semiring-hom.pres-+ (lift 1) (lift m) ⟨
      g .hom (lift (suc m))                ∎
