{-# OPTIONS --safe --no-exact-split #-}
module Order.Constructions.Lex where

open import Cat.Prelude
open import Foundations.Base
open import Meta.Effect

open import Data.Empty
open import Data.Acc as Acc
open import Data.Bool as Bool
open import Data.Dec as Dec
open import Data.Sum.Base as ⊎
open import Data.Sum.Path
open import Data.Nat.Base
open import Data.Nat.Order.Base renaming (_<_ to _<ℕ_)
open import Data.List.Base
open import Data.List.Path
open import Data.List.Operations
open import Data.List.Correspondences.Binary.Prefix

open import Order.Base
open import Order.Strict
open import Order.Total

private variable o ℓ o′ ℓ′ o″ ℓ″ ℓᵢ ℓⱼ ℓₖ : Level

-- pair

×-lex : {P : 𝒰 o} {Q : 𝒰 o′}
      → (_P<_ : P → P → 𝒰 ℓ) → (_Q<_ : Q → Q → 𝒰 ℓ′)
      → P × Q → P × Q → 𝒰 (o ⊔ ℓ ⊔ ℓ′)
×-lex _P<_ _Q<_ (px , qx) (py , qy) = (px P< py) ⊎ ((px ＝ py) × (qx Q< qy))

×-lex-irr : {P : 𝒰 o} {Q : 𝒰 o′}
            {_P<_ : P → P → 𝒰 ℓ} {_Q<_ : Q → Q → 𝒰 ℓ′}
           → (∀ {px} → ¬ (px P< px))
           → (∀ {qx} → ¬ (qx Q< qx))
           → ∀ {pqx}
           → ¬ (×-lex _P<_ _Q<_ pqx pqx)
×-lex-irr pir qir {pqx} (inl p)       = pir p
×-lex-irr pir qir {pqx} (inr (_ , q)) = qir q

×-lex-trans : {P : 𝒰 o} {Q : 𝒰 o′}
              {_P<_ : P → P → 𝒰 ℓ} {_Q<_ : Q → Q → 𝒰 ℓ′}
            → (∀ {px py pz} → px P< py → py P< pz → px P< pz)
            → (∀ {qx qy qz} → qx Q< qy → qy Q< qz → qx Q< qz)
            → ∀ {pqx pqy pqz}
            → ×-lex _P<_ _Q<_ pqx pqy
            → ×-lex _P<_ _Q<_ pqy pqz
            → ×-lex _P<_ _Q<_ pqx pqz
×-lex-trans        ptr qtr      (inl px<py)           (inl py<pz)           =
  inl (ptr px<py py<pz)
×-lex-trans {_P<_} ptr qtr {pqx = (px , _)} (inl px<py)           (inr (py=pz , _))     =
  inl (subst (px P<_) py=pz px<py)
×-lex-trans {_P<_} ptr qtr {pqz = (pz , _)} (inr (px=py , _))     (inl py<pz)           =
  inl (subst (_P< pz) (px=py ⁻¹) py<pz)
×-lex-trans        ptr qtr      (inr (px=py , qx≤qy)) (inr (py=pz , qy≤qz)) =
  inr ( px=py ∙ py=pz , qtr qx≤qy qy≤qz)

-- TODO simplify?
×-ind : {P : 𝒰 o} {Q : 𝒰 o′}
        {_P<_ : P → P → 𝒰 ℓ} {_Q<_ : Q → Q → 𝒰 ℓ′}
      → (∀ {ℓ} {Pp : P → 𝒰 ℓ} → (∀ x → (∀ y → y P< x → Pp y) → Pp x) → ∀ x → Pp x)
      → (∀ {ℓ} {Qp : Q → 𝒰 ℓ} → (∀ x → (∀ y → y Q< x → Qp y) → Qp x) → ∀ x → Qp x)
      → ∀ {ℓ} {PQp : P × Q → 𝒰 ℓ} → (∀ x → (∀ y → ×-lex _P<_ _Q<_ y x → PQp y) → PQp x) → ∀ x → PQp x
×-ind {_P<_} {_Q<_} wp wq {PQp} ih (a , b) =
  ih (a , b) λ where (p , q) →
                      [ (λ p<a → go₁ a p<a q)
                      , (λ where (p=a , q<b) → go₂ p b (go₁ p) q<b)
                      ]ᵤ
  where
  go₂ : ∀ u w → (∀ {v} → v P< u → ∀ w → PQp (v , w))
              → ∀ {z} → z Q< w → PQp (u , z)
  go₂ u w ih₁ =
    wq {Qp = λ x → ∀ {z} → z Q< x → PQp (u , z)}
       (λ x ih₂ {z} z<x →
          ih (u , z) λ where (f , g) →
                               [ (λ f<u → ih₁ f<u g)
                               , (λ where (f=u , g<z) →
                                            subst (λ q → PQp (q , g))
                                                  (f=u ⁻¹)
                                                  (ih₂ z z<x g<z)) ]ᵤ)
       w

  go₁ : ∀ u {v} → v P< u → ∀ w → PQp (v , w)
  go₁ =
    wp λ x ih₁ {v} v<x w →
         ih (_ , w) λ where (f , g) →
                             [ (λ f<v → ih₁ _ v<x f<v g)
                             , (λ where (f=v , g<w) →
                                         go₂ f w
                                          (subst (λ q → ∀ {z} → z P< q → ∀ w → PQp (z , w))
                                                 (f=v ⁻¹)
                                                 (λ {w} → ih₁ v v<x {w}))
                                          g<w) ]ᵤ

×-wf : {P : 𝒰 o} {Q : 𝒰 o′}
       {_P<_ : P → P → 𝒰 ℓ} {_Q<_ : Q → Q → 𝒰 ℓ′}
     → is-wf _P<_
     → is-wf _Q<_
     → is-wf (×-lex _P<_ _Q<_)
×-wf wp wq = from-induction λ P → ×-ind (λ {_} {Pp} → to-induction wp Pp)
                                        (λ {_} {Qp} → to-induction wq Qp)

-- left strict + set, right poset
_<×≤_ : (P : StrictPoset o ℓ) → ⦃ _ : H-Level 2 (StrictPoset.Ob P) ⦄ → Poset o′ ℓ′ → Poset (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
P <×≤ Q = po module <×≤ where
  module P = StrictPoset P
  module Q = Poset Q

  po : Poset _ _
  po .Poset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  po .Poset._≤_ = ×-lex P._<_ Q._≤_
  po .Poset.≤-thin =
    disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
      λ where (px<py , px=py , _) → P.<→≠ px<py px=py
  po .Poset.≤-refl = inr (refl , Q.≤-refl)
  po .Poset.≤-trans {x} {y} = ×-lex-trans P.<-trans Q.≤-trans {pqx = x} {pqy = y}
  po .Poset.≤-antisym (inl px<py)           (inl py<px)       =
    ⊥.rec (P.<-asym px<py py<px)
  po .Poset.≤-antisym (inl px<py)           (inr (py=px , _)) =
    ⊥.rec (P.<→≠ px<py (py=px ⁻¹))
  po .Poset.≤-antisym (inr (px=py , _))     (inl (py<px))     =
    ⊥.rec (P.<→≠ py<px (px=py ⁻¹))
  po .Poset.≤-antisym (inr (px=py , qx≤qy)) (inr (_ , qy≤qx)) =
    ×-path px=py (Q.≤-antisym qx≤qy qy≤qx)
{-# DISPLAY <×≤.po a b = a <×≤ b #-}

-- left set
_<×<_ : (P : StrictPoset o ℓ) → ⦃ _ : H-Level 2 (StrictPoset.Ob P) ⦄ → StrictPoset o′ ℓ′ → StrictPoset (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
P <×< Q = spo module <×< where
  module P = StrictPoset P
  module Q = StrictPoset Q

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  spo .StrictPoset._<_ = ×-lex P._<_ Q._<_
  spo .StrictPoset.<-thin =
    disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
      λ where (px<py , px=py , _) → P.<→≠ px<py px=py
  spo .StrictPoset.<-irrefl {x} = ×-lex-irr {_P<_ = P._<_} {_Q<_ = Q._<_} P.<-irrefl Q.<-irrefl
  spo .StrictPoset.<-trans {x} {y} = ×-lex-trans P.<-trans Q.<-trans {pqx = x} {pqy = y}
{-# DISPLAY <×<.spo a b = a <×< b #-}

-- truncated
-- TODO factor out?
_<×<₁_ : StrictPoset o ℓ → StrictPoset o′ ℓ′ → StrictPoset (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′)
P <×<₁ Q = spo module <×<₁ where
  module P = StrictPoset P
  module Q = StrictPoset Q

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = ⌞ P ⌟ × ⌞ Q ⌟
  spo .StrictPoset._<_ (px , qx) (py , qy) = (px P.< py) ⊎ (∥ px ＝ py ∥₁ × (qx Q.< qy))
  spo .StrictPoset.<-thin =
    disjoint-⊎-is-prop (hlevel 1) (hlevel 1)
      λ where (px<py , px=py₁ , _) → rec! (P.<→≠ px<py) px=py₁
  spo .StrictPoset.<-irrefl (inl px<px)       = P.<-irrefl px<px
  spo .StrictPoset.<-irrefl (inr (_ , qx<qx)) = Q.<-irrefl qx<qx
  spo .StrictPoset.<-trans                (inl px<py)            (inl py<pz)            =
    inl (P.<-trans px<py py<pz)
  spo .StrictPoset.<-trans {x = (px , _)} (inl px<py)            (inr (py=pz₁ , _))     =
    inl (rec! (λ e → subst (px P.<_) e px<py) py=pz₁)
  spo .StrictPoset.<-trans {z = (pz , _)} (inr (px=py₁ , _))     (inl py<pz)            =
    inl (rec! (λ e → subst (P._< pz) (e ⁻¹) py<pz) px=py₁)
  spo .StrictPoset.<-trans                (inr (px=py₁ , qx<qy)) (inr (py=pz₁ , qy<qz)) =
    inr ((do px=py ← px=py₁
             py=pz ← py=pz₁
             pure (px=py ∙ py=pz))
         , Q.<-trans qx<qy qy<qz)
{-# DISPLAY <×<₁.spo a b = a <×<₁ b #-}

-- list

List-lex : {A : 𝒰 o}
         → (_A<_ : A → A → 𝒰 ℓ)
         → List A → List A → 𝒰 (o ⊔ ℓ)
List-lex _A<_ []        ys      = ⊤
List-lex _A<_ (x ∷ xs)  []      = ⊥
List-lex _A<_ (x ∷ xs) (y ∷ ys) = (x A< y) ⊎ ((x ＝ y) × List-lex _A<_ xs ys)

List-lex? : {A : 𝒰 o}
          → (_A=?_ : A → A → Bool)
          → (_A<?_ : A → A → Bool)
          → List A → List A → Bool
List-lex? _A=?_ _A<?_ []        ys      = true
List-lex? _A=?_ _A<?_ (x ∷ xs)  []      = false
List-lex? _A=?_ _A<?_ (x ∷ xs) (y ∷ ys) = (x A<? y) or ((x A=? y) and List-lex? _A=?_ _A<?_ xs ys)

List-lex-refl : {A : 𝒰 o}
                {_A<_ : A → A → 𝒰 ℓ}
              → ∀ {xs} → (List-lex _A<_ xs xs)
List-lex-refl {xs = []} = lift tt
List-lex-refl {xs = x ∷ xs} = inr (refl , List-lex-refl {xs = xs})

List-lex-trans : {A : 𝒰 o}
                 {_A<_ : A → A → 𝒰 ℓ}
               → (∀ {x y z} → x A< y → y A< z → x A< z)
               → ∀ {xs ys zs}
               → List-lex _A<_ xs ys
               → List-lex _A<_ ys zs
               → List-lex _A<_ xs zs
List-lex-trans        xtr {xs = []}                                  xyl                 yzl                = lift tt
List-lex-trans        xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)           (inl y<z)           =
  inl (xtr x<y y<z)
List-lex-trans {_A<_} xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)           (inr (y=z , ys<zs)) =
  inl (subst (x A<_) y=z x<y)
List-lex-trans {_A<_} xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y , xs<ys)) (inl y<z)           =
  inl (subst (_A< z) (x=y ⁻¹) y<z)
List-lex-trans        xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y , xs<ys)) (inr (y=z , ys<zs)) =
  inr ((x=y ∙ y=z) , (List-lex-trans xtr {xs = xs} {ys = ys} {zs = zs} xs<ys ys<zs))

List-lex-antisym : {A : 𝒰 o}
                   {_A<_ : A → A → 𝒰 ℓ}
                 → (∀ {x} → ¬ (x A< x))
                 → (∀ {x y z} → x A< y → y A< z → x A< z)  -- TODO asymmetry?
                 → ∀ {xs ys}
                 → List-lex _A<_ xs ys
                 → List-lex _A<_ ys xs
                 → xs ＝ ys
List-lex-antisym        xir xtr {xs = []}     {ys = []}      xyl                 yxl                = refl
List-lex-antisym        xir xtr {xs = []}     {ys = y ∷ ys}  xyl                 yxl                =
  ⊥.absurd (lower yxl)
List-lex-antisym        xir xtr {xs = x ∷ xs} {ys = []}      xyl                 yxl                =
  ⊥.absurd (lower xyl)
List-lex-antisym        xir xtr {xs = x ∷ xs} {ys = y ∷ ys} (inl x<y)           (inl y<x)           =
  ⊥.absurd (xir (xtr x<y y<x))
List-lex-antisym {_A<_} xir xtr {xs = x ∷ xs} {ys = y ∷ ys} (inl x<y)           (inr (y=x , ys<xs)) =
  ⊥.absurd (xir (subst (x A<_) y=x x<y))
List-lex-antisym {_A<_} xir xtr {xs = x ∷ xs} {ys = y ∷ ys} (inr (x=y , xs<ys)) (inl y<x)           =
 ⊥.absurd (xir (subst (_A< x) (x=y ⁻¹) y<x))
List-lex-antisym        xir xtr {xs = x ∷ xs} {ys = y ∷ ys} (inr (x=y , xs<ys)) (inr (_ , ys<xs))   =
  ap² _∷_ x=y (List-lex-antisym xir xtr xs<ys ys<xs)

List-lex-set-prop : {A : 𝒰 o}
                  → is-set A
                  → {_A<_ : A → A → 𝒰 ℓ}
                  → (∀ {x y} → is-prop (x A< y))
                  → (∀ {x} → ¬ (x A< x))
                  → ∀ {xs ys} → is-prop (List-lex _A<_ xs ys)
List-lex-set-prop as {(_A<_)} ath air {xs = []}                   = hlevel!
List-lex-set-prop as {(_A<_)} ath air {xs = x ∷ xs} {ys = []}     = hlevel!
List-lex-set-prop as {(_A<_)} ath air {xs = x ∷ xs} {ys = y ∷ ys} =
  disjoint-⊎-is-prop ath
    (×-is-of-hlevel 1 (as x y) (List-lex-set-prop as ath air {xs = xs} {ys = ys}))
    λ where (x<y , x=y , _) → air (subst (x A<_) (x=y ⁻¹) x<y)

-- ++ interaction

List-lex-++-r : {A : 𝒰 o}
                {_A<_ : A → A → 𝒰 ℓ}
              → ∀ {xs ys}
              → List-lex _A<_ xs (xs ++ ys)
List-lex-++-r {xs = []}     = lift tt
List-lex-++-r {xs = x ∷ xs} = inr (refl , List-lex-++-r {xs = xs})

-- TODO is this too strong?
List-lex-compare : {A : 𝒰 o}
                 → {_A<_ : A → A → 𝒰 ℓ}
                 → (∀ {x y} → Dec (x A< y))
                 → (∀ {x y} → ¬ (x A< y) → ¬ (y A< x) → x ＝ y)
                 → ∀ {xs ys} → List-lex _A<_ xs ys ⊎ List-lex _A<_ ys xs
List-lex-compare d cx {xs = []}                   = inl (lift tt)
List-lex-compare d cx {xs = x ∷ xs} {ys = []}     = inr (lift tt)
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} with d {x} {y}
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} | yes x<y = inl (inl x<y)
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y with d {y} {x}
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | yes y<x = inr (inl y<x)
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | no y≮x with List-lex-compare d cx {xs = xs} {ys = ys}
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | no y≮x | inl xs≤ys =
  inl (inr (cx x≮y y≮x , xs≤ys))
List-lex-compare d cx {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | no y≮x | inr ys≤xs =
  inr (inr (cx y≮x x≮y , ys≤xs))

List-lex-dec : {A : 𝒰 o}
             → is-discrete A
             → {_A<_ : A → A → 𝒰 ℓ}
             → (∀ {x y} → Dec (x A< y))
             → ∀ {xs ys} → Dec (List-lex _A<_ xs ys)
List-lex-dec da d {xs = []}     {ys = ys}     = yes (lift tt)
List-lex-dec da d {xs = x ∷ xs} {ys = []}     = no lower
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} with d {x} {y}
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | yes x<y = yes (inl x<y)
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y with da {x} {y}
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | yes x=y with List-lex-dec da (λ {x} {y} → d {x} {y}) {xs = xs} {ys = ys}
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | yes x=y | yes xs≤ys = yes (inr (x=y , xs≤ys))
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | yes x=y | no xs≰ys = no [ x≮y , xs≰ys ∘ snd ]ᵤ
List-lex-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no  x≮y | no x≠y = no [ x≮y , x≠y ∘ fst ]ᵤ

-- set

[]≤ : (A : StrictPoset o ℓ) → ⦃ _ : H-Level 2 (StrictPoset.Ob A) ⦄
    → Poset o (o ⊔ ℓ)
[]≤ A = po module []≤ where
  module A = StrictPoset A

  po : Poset _ _
  po .Poset.Ob = List ⌞ A ⌟
  po .Poset._≤_ = List-lex A._<_
  po .Poset.≤-thin {x} {y} = List-lex-set-prop hlevel! A.<-thin A.<-irrefl {xs = x} {ys = y}
  po .Poset.≤-refl {x} = List-lex-refl {xs = x}
  po .Poset.≤-trans {x} {y} {z} = List-lex-trans A.<-trans {xs = x} {ys = y} {zs = z}
  po .Poset.≤-antisym = List-lex-antisym A.<-irrefl A.<-trans

[]≤-dto : {A : StrictPoset o ℓ}
        → ⦃ sa : H-Level 2 (StrictPoset.Ob A) ⦄
        → is-decidable-strict-total-order A
        → is-decidable-total-order ([]≤ A)
[]≤-dto dsto =
  dec+total→dec-total-order
    (λ {x} {y} → List-lex-dec (dsto .is-decidable-strict-total-order.has-discrete)
                              (dsto .is-decidable-strict-total-order.dec-<)
                              {xs = x} {ys = y})
    (record { compare = λ x y →
       List-lex-compare (dsto .is-decidable-strict-total-order.dec-<)
                        (dsto .is-decidable-strict-total-order.<-connex)
                        {xs = x} {ys = y} })

-- TODO trunc

-- strict

List-lex< : {A : 𝒰 o}
          → (_A<_ : A → A → 𝒰 ℓ)
          → List A → List A → 𝒰 (o ⊔ ℓ)
List-lex< _A<_ xs        []      = ⊥
List-lex< _A<_ []       (y ∷ ys) = ⊤
List-lex< _A<_ (x ∷ xs) (y ∷ ys) = (x A< y) ⊎ ((x ＝ y) × List-lex< _A<_ xs ys)

List-lex<? : {A : 𝒰 o}
           → (_A=?_ : A → A → Bool)
           → (_A<?_ : A → A → Bool)
           → List A → List A → Bool
List-lex<? _A=?_ _A<?_ xs        []      = false
List-lex<? _A=?_ _A<?_ []       (y ∷ ys) = true
List-lex<? _A=?_ _A<?_ (x ∷ xs) (y ∷ ys) = (x A<? y) or ((x A=? y) and List-lex<? _A=?_ _A<?_ xs ys)

List-lex<-irr : {A : 𝒰 o}
                {_A<_ : A → A → 𝒰 ℓ}
              → (∀ {x} → ¬ (x A< x))
              → ∀ {xs} → ¬ (List-lex< _A<_ xs xs)
List-lex<-irr xir {xs = x ∷ xs} (inl l)       = xir l
List-lex<-irr xir {xs = x ∷ xs} (inr (_ , r)) = List-lex<-irr xir {xs = xs} r

List-lex<-trans : {A : 𝒰 o}
                  {_A<_ : A → A → 𝒰 ℓ}
                → (∀ {x y z} → x A< y → y A< z → x A< z)
                → ∀ {xs ys zs}
                → List-lex< _A<_ xs ys
                → List-lex< _A<_ ys zs
                → List-lex< _A<_ xs zs
List-lex<-trans        xtr {xs = []}     {ys = y ∷ ys} {zs = z ∷ zs}  xyl                  yzl                =
  lift tt
List-lex<-trans        xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)            (inl y<z)           =
  inl (xtr x<y y<z)
List-lex<-trans {_A<_} xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)            (inr (y=z , ys<zs)) =
  inl (subst (x A<_) y=z x<y)
List-lex<-trans {_A<_} xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y , xs<ys))  (inl y<z)           =
  inl (subst (_A< z) (x=y ⁻¹) y<z)
List-lex<-trans        xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y , xs<ys))  (inr (y=z , ys<zs)) =
  inr ((x=y ∙ y=z) , (List-lex<-trans xtr {xs = xs} {ys = ys} {zs = zs} xs<ys ys<zs))

List-lex<-set-prop : {A : 𝒰 o}
                  → is-set A
                  → {_A<_ : A → A → 𝒰 ℓ}
                  → (∀ {x y} → is-prop (x A< y))
                  → (∀ {x} → ¬ (x A< x))
                  → ∀ {xs ys} → is-prop (List-lex< _A<_ xs ys)
List-lex<-set-prop as {_A<_} ath air               {ys = []}     = hlevel!
List-lex<-set-prop as {_A<_} ath air {xs = []}     {ys = y ∷ ys} = hlevel!
List-lex<-set-prop as {_A<_} ath air {xs = x ∷ xs} {ys = y ∷ ys} =
  disjoint-⊎-is-prop ath
    (×-is-of-hlevel 1 (as x y) (List-lex<-set-prop as ath air {xs = xs} {ys = ys}))
    λ where (x<y , x=y , _) → air (subst (x A<_) (x=y ⁻¹) x<y)

List-lex<-++-r : {A : 𝒰 o}
                 {_A<_ : A → A → 𝒰 ℓ}
               → ∀ {xs ys}
               → 0 <ℕ length ys
               → List-lex< _A<_ xs (xs ++ ys)
List-lex<-++-r               {ys = []}     ly = ⊥.absurd (≮z ly)
List-lex<-++-r {xs = []}     {ys = y ∷ ys} _  = lift tt
List-lex<-++-r {xs = x ∷ xs} {ys = y ∷ ys} _  = inr (refl , (List-lex<-++-r {xs = xs} {ys = y ∷ ys} z<s))

opaque
  unfolding Prefix1
  List-lex<-prefix1 : {A : 𝒰 o}
                      {_A<_ : A → A → 𝒰 ℓ}
                    → ∀ {xs ys}
                    → Prefix1 xs ys
                    → List-lex< _A<_ xs ys
  List-lex<-prefix1 {_A<_} {xs} (t , txy , exy) =
    subst (List-lex< _A<_ xs) exy $
    List-lex<-++-r {xs = xs} {ys = t ∷ txy} z<s

-- strict truncated

List-lex<₁ : {A : 𝒰 o}
         → (_A<_ : A → A → 𝒰 ℓ)
         → List A → List A → 𝒰 (o ⊔ ℓ)
List-lex<₁ _A<_ xs        []      = ⊥
List-lex<₁ _A<_ []       (y ∷ ys) = ⊤
List-lex<₁ _A<_ (x ∷ xs) (y ∷ ys) = (x A< y) ⊎ (∥ x ＝ y ∥₁ × List-lex<₁ _A<_ xs ys)

List-lex<₁-irr : {A : 𝒰 o}
               {_A<_ : A → A → 𝒰 ℓ}
             → (∀ {x} → ¬ (x A< x))
             → ∀ {xs} → ¬ (List-lex<₁ _A<_ xs xs)
List-lex<₁-irr xir {xs = x ∷ xs} (inl l)       = xir l
List-lex<₁-irr xir {xs = x ∷ xs} (inr (_ , r)) = List-lex<₁-irr xir {xs = xs} r

List-lex<₁-trans : {A : 𝒰 o}
                 {_A<_ : A → A → 𝒰 ℓ}
               → (∀ {x y} → is-prop (x A< y))
               → (∀ {x y z} → x A< y → y A< z → x A< z)
               → ∀ {xs ys zs}
               → List-lex<₁ _A<_ xs ys
               → List-lex<₁ _A<_ ys zs
               → List-lex<₁ _A<_ xs zs
List-lex<₁-trans        xth xtr {xs = []}     {ys = y ∷ ys} {zs = z ∷ zs}  xyl                  yzl                =
  lift tt
List-lex<₁-trans        xth xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)            (inl y<z)           =
  inl (xtr x<y y<z)
List-lex<₁-trans {_A<_} xth xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inl x<y)            (inr (y=z₁ , ys<zs)) =
  inl (∥-∥₁.elim (λ _ → xth)
                 (λ y=z → subst (x A<_) y=z x<y)
                 y=z₁)
List-lex<₁-trans {_A<_} xth xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y₁ , xs<ys))  (inl y<z)           =
  inl (∥-∥₁.elim (λ _ → xth)
                 (λ x=y → subst (_A< z) (x=y ⁻¹) y<z)
                 x=y₁)
List-lex<₁-trans        xth xtr {xs = x ∷ xs} {ys = y ∷ ys} {zs = z ∷ zs} (inr (x=y₁ , xs<ys))  (inr (y=z₁ , ys<zs)) =
  inr ( (do x=y ← x=y₁
            y=z ← y=z₁
            pure (x=y ∙ y=z))
      , List-lex<₁-trans xth xtr {xs = xs} {ys = ys} {zs = zs} xs<ys ys<zs)

List-lex<₁-prop : {A : 𝒰 o}
               → {_A<_ : A → A → 𝒰 ℓ}
               → (∀ {x y} → is-prop (x A< y))
               → (∀ {x} → ¬ (x A< x))
               → ∀ {xs ys} → is-prop (List-lex<₁ _A<_ xs ys)
List-lex<₁-prop {_A<_} ath air               {ys = []}     = hlevel!
List-lex<₁-prop {_A<_} ath air {xs = []}     {ys = y ∷ ys} = hlevel!
List-lex<₁-prop {_A<_} ath air {xs = x ∷ xs} {ys = y ∷ ys} =
  disjoint-⊎-is-prop ath
    (×-is-of-hlevel 1 hlevel! (List-lex<₁-prop ath air {xs = xs} {ys = ys}))
    λ where (x<y , x=y₁ , _) → rec! (λ x=y → air (subst (x A<_) (x=y ⁻¹) x<y)) x=y₁

-- set

[]< : (A : StrictPoset o ℓ) → ⦃ _ : H-Level 2 (StrictPoset.Ob A) ⦄
    → StrictPoset o (o ⊔ ℓ)
[]< A = spo module []< where
  module A = StrictPoset A

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = List ⌞ A ⌟
  spo .StrictPoset._<_ = List-lex< A._<_
  spo .StrictPoset.<-thin {x} {y} = List-lex<-set-prop hlevel! A.<-thin A.<-irrefl {xs = x} {ys = y}
  spo .StrictPoset.<-irrefl {x} = List-lex<-irr A.<-irrefl {xs = x}
  spo .StrictPoset.<-trans {x} {y} {z} = List-lex<-trans A.<-trans {xs = x} {ys = y} {zs = z}

-- weak linearity seems unprovable without decidability

List-lex<-connex : {A : 𝒰 o}
                  {_A<_ : A → A → 𝒰 ℓ}
                → (∀ {x y} → ¬ (x A< y) → ¬ (y A< x) → x ＝ y)
                → ∀ {xs ys} → ¬ (List-lex< _A<_ xs ys) → ¬ (List-lex< _A<_ ys xs) → xs ＝ ys
List-lex<-connex cn {xs = []}     {ys = []}     nxy nyx = refl
List-lex<-connex cn {xs = []}     {ys = x ∷ ys} nxy nyx = ⊥.absurd (nxy (lift tt))
List-lex<-connex cn {xs = x ∷ xs} {ys = []}     nxy nyx = ⊥.absurd (nyx (lift tt))
List-lex<-connex cn {xs = x ∷ xs} {ys = y ∷ ys} nxy nyx =
  let x=y = cn (⊥.contra inl nxy) (⊥.contra inl nyx) in
  ap² _∷_ x=y
          (List-lex<-connex cn {xs = xs} {ys = ys}
                           (⊥.contra (λ xs<ys → inr (x=y , xs<ys)) nxy)
                           (⊥.contra (λ ys<xs → inr (x=y ⁻¹ , ys<xs)) nyx))

List-lex<-dec : {A : 𝒰 o}
             → is-discrete A
             → {_A<_ : A → A → 𝒰 ℓ}
             → (∀ {x y} → Dec (x A< y))
             → ∀ {xs ys} → Dec (List-lex< _A<_ xs ys)
List-lex<-dec da d {xs = xs} {ys = []}     = no lower
List-lex<-dec da d {xs = []} {ys = y ∷ ys} = yes (lift tt)
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} with d {x} {y}
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | yes x<y = yes (inl x<y)
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no x≮y with da {x} {y}
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no x≮y | yes x=y with List-lex<-dec da (λ {x} {y} → d {x} {y}) {xs = xs} {ys = ys}
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no x≮y | yes x=y | yes xs<ys = yes (inr (x=y , xs<ys))
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no x≮y | yes x=y | no  xs≮ys = no [ x≮y , xs≮ys ∘ snd ]ᵤ
List-lex<-dec da d {xs = x ∷ xs} {ys = y ∷ ys} | no x≮y | no x≠y = no [ x≮y , x≠y ∘ fst ]ᵤ

[]<-dsto : {A : StrictPoset o ℓ}
          → ⦃ sa : H-Level 2 (StrictPoset.Ob A) ⦄
          → is-decidable-strict-total-order A
          → is-decidable-strict-total-order ([]< A)
[]<-dsto dsto =
  discrete+dec+connnex→dec-strict-total-order
    List-is-discrete
    (λ {x} {y} → List-lex<-dec (dsto .is-decidable-strict-total-order.has-discrete)
                              (dsto .is-decidable-strict-total-order.dec-<)
                              {xs = x} {ys = y})
    (List-lex<-connex (dsto .is-decidable-strict-total-order.<-connex))

-- trunс

[]<₁ : StrictPoset o ℓ → StrictPoset o (o ⊔ ℓ)
[]<₁ A = spo module []<₁ where
  module A = StrictPoset A

  spo : StrictPoset _ _
  spo .StrictPoset.Ob = List ⌞ A ⌟
  spo .StrictPoset._<_ = List-lex<₁ A._<_
  spo .StrictPoset.<-thin {x} {y} = List-lex<₁-prop A.<-thin A.<-irrefl {xs = x} {ys = y}
  spo .StrictPoset.<-irrefl {x} = List-lex<₁-irr A.<-irrefl {xs = x}
  spo .StrictPoset.<-trans {x} {y} {z} = List-lex<₁-trans (hlevel 1) A.<-trans {xs = x} {ys = y} {zs = z}

-- interaction

List-lex-≤→≯ : {A : 𝒰 o}
             → {_A<_ : A → A → 𝒰 ℓ}
             → (∀ {x} → ¬ (x A< x))
             → (∀ {x y z} → x A< y → y A< z → x A< z)  -- TODO asymmetry?
             → ∀ {xs ys} → List-lex _A<_ xs ys → ¬ (List-lex< _A<_ ys xs)
List-lex-≤→≯        ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inl x<y)         (inl y<x)         =
  ir (tr x<y y<x)
List-lex-≤→≯ {_A<_} ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inl x<y)         (inr (y=x , yxs)) =
  ir (subst (x A<_) y=x x<y)
List-lex-≤→≯ {_A<_} ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inr (x=y , xys)) (inl y<x)         =
  ir (subst (_A< x) (x=y ⁻¹) y<x)
List-lex-≤→≯        ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inr (x=y , xys)) (inr (y=x , yxs)) =
  List-lex-≤→≯ ir tr {xs = xs} {ys = ys} xys yxs

List-lex-<→≱ : {A : 𝒰 o}
             → {_A<_ : A → A → 𝒰 ℓ}
             → (∀ {x} → ¬ (x A< x))
             → (∀ {x y z} → x A< y → y A< z → x A< z)  -- TODO asymmetry?
             → ∀ {xs ys} → List-lex< _A<_ xs ys → ¬ (List-lex _A<_ ys xs)
List-lex-<→≱        ir tr {xs = []}     {ys = []}      xys               yxs              = lower xys
List-lex-<→≱        ir tr {xs = []}     {ys = y ∷ ys}  xys               yxs              = lower yxs
List-lex-<→≱        ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inl x<y)         (inl y<x)         =
  ir (tr x<y y<x)
List-lex-<→≱ {_A<_} ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inl x<y)         (inr (y=x , yxs)) =
  ir (subst (x A<_) y=x x<y)
List-lex-<→≱ {_A<_} ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inr (x=y , xys)) (inl y<x)         =
  ir (subst (_A< x) (x=y ⁻¹) y<x)
List-lex-<→≱        ir tr {xs = x ∷ xs} {ys = y ∷ ys} (inr (x=y , xys)) (inr (y=x , yxs)) =
  List-lex-<→≱ ir tr {xs = xs} {ys = ys} xys yxs

-- TODO the other directions seem to require DSTO

-- TODO qlex
