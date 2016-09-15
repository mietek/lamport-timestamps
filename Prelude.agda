module Prelude where

open import Agda.Builtin.IO public
  using (IO)

open import Data.Empty public using ()
  renaming (⊥ to 𝟘 ; ⊥-elim to elim𝟘)

open import Data.Nat public
  using (ℕ ; zero ; suc ; decTotalOrder ; _⊔_)
  renaming (_≤_ to _⊑_ ; z≤n to z⊑n ; s≤s to n⊑m→sn⊑sm ;
            _≤′_ to _≤_ ; ≤′-refl to refl≤ ; ≤′-step to step≤ ;
            _≤?_ to _⊑?_ ; _≰_ to _⋢_ ; _<′_ to _<_ ; _≟_ to _≡?_)

open import Data.Nat.Properties public using ()
  renaming (≤⇒≤′ to ⊑→≤ ; ≤′⇒≤ to ≤→⊑ ; z≤′n to z≤n ; s≤′s to n≤m→sn≤sm)

open import Data.Nat.Show public
  using (show)

open import Data.Product public
  using (Σ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂)

open import Data.String public
  using (String)
  renaming (_≟_ to _≡ₛ?_ ; _++_ to _⧺_)

open import Data.Sum public
  using (_⊎_)
  renaming (inj₁ to ι₁ ; inj₂ to ι₂)

open import Data.Unit public using ()
  renaming (⊤ to Unit ; tt to unit)

open import Function public
  using (_∘_)

open import Relation.Binary public
  using (Antisymmetric ; Decidable ; DecTotalOrder ; Reflexive ; Rel ;
         Symmetric ; Total ; Transitive ; Trichotomous ; Tri)
  renaming (tri< to τ₍ ; tri≈ to τ₌ ; tri> to τ₎)

open module NDTO = DecTotalOrder decTotalOrder public using ()
  renaming (antisym to antisym⊑ ; trans to trans⊑ ; total to total⊑)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂ ; subst)

open import Relation.Binary.HeterogeneousEquality public
  using (_≅_ ; _≇_)
  renaming (refl to refl≅ ; trans to trans≅ ; sym to sym≅ ; cong to cong≅ ;
            cong₂ to cong₂≅ ; subst to subst≅ ; ≅-to-≡ to ≅→≡ ; ≡-to-≅ to ≡→≅)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

open import Relation.Nullary.Negation public using ()
  renaming (contradiction to _↯_)


-- I/O.

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _≫=_   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILED return (\_ _ -> return)    #-}
{-# COMPILED _≫=_   (\_ _ _ _ -> (>>=)) #-}

_≫_ : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
m₁ ≫ m₂ = m₁ ≫= λ _ → m₂

postulate
  putStr   : String → IO Unit
  putStrLn : String → IO Unit

{-# COMPILED putStr   putStr   #-}
{-# COMPILED putStrLn putStrLn #-}


-- Notation for I/O.

infix -10 do_
do_ : ∀ {a} {A : Set a} → A → A
do x = x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

infixr 0 do-bind
syntax do-bind m₁ (λ x → m₂) = x ← m₁ ⁏ m₂
do-bind = _≫=_

infixr 0 do-seq
syntax do-seq m₁ m₂ = m₁ ⁏ m₂
do-seq = _≫_

infixr 0 do-let
syntax do-let m₁ (λ x → m₂) = x := m₁ ⁏ m₂
do-let = case_of_


-- Properties of binary relations.

Irreflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Irreflexive _∼_ = ∀ {x} → ¬ (x ∼ x)


-- Properties of _≡_.

n≡m→sn≡sm : ∀ {n m} → n ≡ m → suc n ≡ suc m
n≡m→sn≡sm refl = refl

sn≡sm→n≡m : ∀ {n m} → suc n ≡ suc m → n ≡ m
sn≡sm→n≡m refl = refl

n≢m→sn≢sm : ∀ {n m} → n ≢ m → suc n ≢ suc m
n≢m→sn≢sm n≢m refl = refl ↯ n≢m

sn≢sm→n≢m : ∀ {n m} → suc n ≢ suc m → n ≢ m
sn≢sm→n≢m sn≢sm refl = refl ↯ sn≢sm

sym≢ : ∀ {a} {A : Set a} → Symmetric (_≢_ {A = A})
sym≢ x≢y refl = refl ↯ x≢y


-- Properties of _≤_.

_≰_ : ℕ → ℕ → Set
n ≰ m = ¬ (n ≤ m)

sn≤m→n≤m : ∀ {n m} → suc n ≤ m → n ≤ m
sn≤m→n≤m refl≤        = step≤ refl≤
sn≤m→n≤m (step≤ sn≤m) = step≤ (sn≤m→n≤m sn≤m)

sn≤sm→n≤m : ∀ {n m} → suc n ≤ suc m → n ≤ m
sn≤sm→n≤m refl≤        = refl≤
sn≤sm→n≤m (step≤ sn≤m) = sn≤m→n≤m sn≤m

n≰m→sn≰sm : ∀ {n m} → n ≰ m → suc n ≰ suc m
n≰m→sn≰sm n≰m refl≤        = refl≤ ↯ n≰m
n≰m→sn≰sm n≰m (step≤ sn≤m) = sn≤m→n≤m sn≤m ↯ n≰m

sn≰sm→n≰m : ∀ {n m} → suc n ≰ suc m → n ≰ m
sn≰sm→n≰m sn≰sm refl≤       = refl≤ ↯ sn≰sm
sn≰sm→n≰m sn≰sm (step≤ n≤m) = sn≰sm→n≰m (sn≰sm ∘ step≤) n≤m

sn≰n : ∀ {n} → suc n ≰ n
sn≰n {zero}  = λ ()
sn≰n {suc n} = n≰m→sn≰sm sn≰n

n≤m⊔n : (n m : ℕ) → n ≤ m ⊔ n
n≤m⊔n zero    zero    = refl≤
n≤m⊔n zero    (suc m) = z≤n
n≤m⊔n (suc n) zero    = refl≤
n≤m⊔n (suc n) (suc m) = n≤m→sn≤sm (n≤m⊔n n m)


-- Properties of _<_.

_≮_ : ℕ → ℕ → Set
n ≮ m = ¬ (n < m)

z<sn : ∀ {n} → zero < suc n
z<sn = n≤m→sn≤sm z≤n

n<m→sn<sm : ∀ {n m} → n < m → suc n < suc m
n<m→sn<sm = n≤m→sn≤sm

sn<m→n<m : ∀ {n m} → suc n < m → n < m
sn<m→n<m = sn≤m→n≤m

sn<sm→n<m : ∀ {n m} → suc n < suc m → n < m
sn<sm→n<m = sn≤sm→n≤m

n≮m→sn≮sm : ∀ {n m} → n ≮ m → suc n ≮ suc m
n≮m→sn≮sm = n≰m→sn≰sm

sn≮sm→n≮m : ∀ {n m} → suc n ≮ suc m → n ≮ m
sn≮sm→n≮m = sn≰sm→n≰m

n<s[n⊔m] : (n m : ℕ) → n < suc (n ⊔ m)
n<s[n⊔m] zero    zero    = refl≤
n<s[n⊔m] zero    (suc m) = n≤m→sn≤sm z≤n
n<s[n⊔m] (suc n) zero    = refl≤
n<s[n⊔m] (suc n) (suc m) = n≤m→sn≤sm (n<s[n⊔m] n m)


-- Conversion between _⊑_, ⊏, _≤_, _<_, and _≡_.

≰→⋢ : ∀ {n m} → n ≰ m → n ⋢ m
≰→⋢ {zero}  {zero}  n≰m = refl≤ ↯ n≰m
≰→⋢ {suc n} {zero}  n≰m = λ ()
≰→⋢ {n}     {suc m} n≰m = λ n⊑m → ⊑→≤ n⊑m ↯ n≰m

⋢→≰ : ∀ {n m} → n ⋢ m → n ≰ m
⋢→≰ {zero}  {m}     n⋢m = z⊑n ↯ n⋢m
⋢→≰ {suc n} {zero}  n⋢m = λ ()
⋢→≰ {suc n} {suc m} n⋢m = λ n≤m → ≤→⊑ n≤m ↯ n⋢m

≤×≢→< : ∀ {n m} → n ≤ m → n ≢ m → n < m
≤×≢→< refl≤       n≢m = refl ↯ n≢m
≤×≢→< (step≤ n≤m) n≢m = n≤m→sn≤sm n≤m

≤→<⊎≡ : ∀ {n m} → n ≤ m → n < m ⊎ n ≡ m
≤→<⊎≡ refl≤       = ι₂ refl
≤→<⊎≡ (step≤ n≤m) with ≤→<⊎≡ n≤m
≤→<⊎≡ (step≤ n≤m) | ι₁ sn≤m = ι₁ (step≤ sn≤m)
≤→<⊎≡ (step≤ n≤m) | ι₂ refl = ι₁ refl≤

<→≤ : ∀ {n m} → n < m → n ≤ m
<→≤ n<m = sn≤m→n≤m n<m

≡→≤ : ∀ {n m} → n ≡ m → n ≤ m
≡→≤ refl = refl≤


-- _≤_ is a decidable non-strict total order on naturals.

antisym≤ : Antisymmetric _≡_ _≤_
antisym≤ n≤m m≤n = antisym⊑ (≤→⊑ n≤m) (≤→⊑ m≤n)

total≤ : Total _≤_
total≤ n m with total⊑ n m
total≤ n m | ι₁ n⊑m = ι₁ (⊑→≤ n⊑m)
total≤ n m | ι₂ m⊑n = ι₂ (⊑→≤ m⊑n)

trans≤ : Transitive _≤_
trans≤ n≤m m≤z = ⊑→≤ (trans⊑ (≤→⊑ n≤m) (≤→⊑ m≤z))

_≤?_ : Decidable _≤_
n ≤? m with n ⊑? m
n ≤? m | yes n⊑m = yes (⊑→≤ n⊑m)
n ≤? m | no  n⋢m = no (⋢→≰ n⋢m)


-- _<_ is a decidable strict total order on naturals.

trans< : Transitive _<_
trans< n<m m<l = trans≤ (step≤ n<m) m<l

tri< : Trichotomous _≡_ _<_
tri< zero    zero    = τ₌ (λ ()) refl   (λ ())
tri< zero    (suc m) = τ₍ z<sn   (λ ()) (λ ())
tri< (suc n) zero    = τ₎ (λ ()) (λ ()) z<sn
tri< (suc n) (suc m) with tri< n m
tri< (suc n) (suc m) | τ₍ n<m n≢m m≮n = τ₍ (n<m→sn<sm n<m) (n≢m→sn≢sm n≢m) (n≮m→sn≮sm m≮n)
tri< (suc n) (suc m) | τ₌ n≮m n≡m m≮n = τ₌ (n≮m→sn≮sm n≮m) (n≡m→sn≡sm n≡m) (n≮m→sn≮sm m≮n)
tri< (suc n) (suc m) | τ₎ n≮m n≢m m<n = τ₎ (n≮m→sn≮sm n≮m) (n≢m→sn≢sm n≢m) (n<m→sn<sm m<n)

irrefl< : Irreflexive _<_
irrefl< = sn≰n

_<?_ : Decidable _<_
n <? m = suc n ≤? m
