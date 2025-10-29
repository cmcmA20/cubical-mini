{-# OPTIONS --safe --no-exact-split #-}
module Order.Constructions.Lex.Vec where

open import Cat.Prelude
open import Foundations.Base
open import Meta.Effect

open import Data.Empty
open import Data.Acc as Acc
open import Data.Dec as Dec
open import Data.Sum.Base as ⊎
open import Data.Sum.Path
open import Data.Nat.Base
open import Data.Nat.Order.Base renaming (_<_ to _<ℕ_)
open import Data.Fin.Inductive
open import Data.Vec.Inductive
open import Data.Vec.Inductive.Operations

open import Order.Constructions.Lex

private variable o ℓ o′ ℓ′ o″ ℓ″ ℓᵢ ℓⱼ ℓₖ : Level

-- TODO other variants

-- strict

Vec-lex< : {A : 𝒰 o} {n : ℕ}
         → (_A<_ : A → A → 𝒰 ℓ)
         → Vec A n → Vec A n → 𝒰 (o ⊔ ℓ)
Vec-lex< {n = zero}  _A<_ []       []       = ⊥
Vec-lex< {n = suc n} _A<_ (x ∷ xs) (y ∷ ys) = (x A< y) ⊎ ((x ＝ y) × Vec-lex< _A<_ xs ys)

Vec-lex<-irr : {A : 𝒰 o} {n : ℕ}
               {_A<_ : A → A → 𝒰 ℓ}
             → (∀ {x} → ¬ (x A< x))
             → {xs : Vec A n} → ¬ (Vec-lex< _A<_ xs xs)
Vec-lex<-irr {n = zero}  xir {xs = []} prf = lower prf
Vec-lex<-irr {n = suc n} xir {xs = x ∷ xs} (inl l)       = xir l
Vec-lex<-irr {n = suc n} xir {xs = x ∷ xs} (inr (_ , r)) = Vec-lex<-irr xir {xs = xs} r

Vec-lex<-trans : {A : 𝒰 o} {n : ℕ}
                 {_A<_ : A → A → 𝒰 ℓ}
               → (∀ {x y z} → x A< y → y A< z → x A< z)
               → {xs ys zs : Vec A n}
               → Vec-lex< _A<_ xs ys
               → Vec-lex< _A<_ ys zs
               → Vec-lex< _A<_ xs zs
Vec-lex<-trans {n = zero}         atr {xs = []}     {ys = []}     {zs = []}      xys                 yzs                = xys
Vec-lex<-trans {n = suc n}        atr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)           (inl y<z)           =
  inl (atr x<y y<z)
Vec-lex<-trans {n = suc n} {_A<_} atr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)           (inr (y=z , ys<zs)) =
  inl (subst (x A<_) y=z x<y)
Vec-lex<-trans {n = suc n} {_A<_} atr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y , xs<ys)) (inl y<z)           =
  inl (subst (_A< z) (x=y ⁻¹) y<z)
Vec-lex<-trans {n = suc n}        atr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y , xs<ys)) (inr (y=z , ys<zs)) =
  inr (x=y ∙ y=z , Vec-lex<-trans atr {xs = xs} {ys = ys} {zs = zs} xs<ys ys<zs)

-- TODO Vec-lex<-set-prop

Vec-lex<-ind : {A : 𝒰 o} {_A<_ : A → A → 𝒰 ℓ} {n : ℕ}
             → (∀ {ℓ} {P : A → 𝒰 ℓ} → (∀ x → (∀ y → y A< x → P y) → P x) → ∀ x → P x)
             → ∀ {ℓ} {P : Vec A n → 𝒰 ℓ} → (∀ xs → (∀ ys → Vec-lex< _A<_ ys xs → P ys) → P xs) → ∀ xs → P xs
Vec-lex<-ind {n = zero}  ap ih []       =
  ih [] λ where [] lt → absurd (lower lt)
Vec-lex<-ind {n = suc n} ap {P} ih (x ∷ xs) =
  ×-ind ap (Vec-lex<-ind {n = n} ap)
           {PQp = λ (a , as) → P (a ∷ as)}
           (λ where (a , as) ih' →
                       ih (a ∷ as) λ where (y ∷ ys) → ih' (y , ys))
           (x , xs)

Vec-lex<-wf : {A : 𝒰 o} {_A<_ : A → A → 𝒰 ℓ} {n : ℕ}
            → is-wf _A<_
            → is-wf (Vec-lex< {n = n} _A<_)
Vec-lex<-wf wa =
  from-induction λ P → Vec-lex<-ind (λ {_} {P} → to-induction wa P)

-- prefix

Vec-lex<-prefix-lup : {A : 𝒰 o} {_A<_ : A → A → 𝒰 ℓ} {n : ℕ}
                    → {xs ys : Vec A n}
                    → (f : Fin n)
                    → (∀ j → fin→ℕ j <ℕ fin→ℕ f → lookup xs j ＝ lookup ys j)
                    → lookup xs f A< lookup ys f
                    → Vec-lex< _A<_ xs ys
Vec-lex<-prefix-lup {n = suc n} {x ∷ xs} {y ∷ ys}  fzero   pre flt =
  inl flt
Vec-lex<-prefix-lup {n = suc n} {x ∷ xs} {y ∷ ys} (fsuc f) pre flt =
  inr (  pre fzero z<s
       , Vec-lex<-prefix-lup {n = n} {xs = xs} {ys = ys}
                             f
                             (λ j jlt → pre (fsuc j) (s<s jlt))
                             flt)

Vec-lex<-prefix-++ : {A : 𝒰 o} {_A<_ : A → A → 𝒰 ℓ} {k m : ℕ}
                → {xs : Vec A k} {as bs : Vec A m} {a b : A}
                → a A< b
                → Vec-lex< _A<_ (xs ++ (a ∷ as)) (xs ++ (b ∷ bs))
Vec-lex<-prefix-++ {k = zero}  {xs = []}     a<b =
  inl a<b
Vec-lex<-prefix-++ {k = suc k} {xs = x ∷ xs} a<b =
  inr (refl , Vec-lex<-prefix-++ {xs = xs} a<b)
