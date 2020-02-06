module semantics-with-waist where

open import Level renaming (_⊔_ to _⊍_; suc to ℓsuc; zero to ℓ₀)
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_)

-- “s ≔ v” is just a way to document v with string s.
open import Data.String using (String)
_≔_ : ∀ {ℓ} {A : Set ℓ} → String → A → A
s ≔ v = v
infix 9 _≔_

-- Used in an example later on; too boring to be placed there.
data Digit : Set where
  #0 #1 #2 #3 #4 #5 #6 #7 #8 #9 : Digit

#→ℕ : Digit → ℕ
#→ℕ #0 = 0
#→ℕ #1 = 1
#→ℕ #2 = 2
#→ℕ #3 = 3
#→ℕ #4 = 4
#→ℕ #5 = 5
#→ℕ #6 = 6
#→ℕ #7 = 7
#→ℕ #8 = 8
#→ℕ #9 = 9

import Data.Unit as Unit
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₘ_)

-- Single argument application
_app_ : Term → Term → Term
(def f args) app args′ = def f (arg (arg-info visible relevant) args′ ∷ [])
{-# CATCHALL #-}
tm app args = tm

-- Reify ℕ term encodings as ℕ values
toℕ : Term → ℕ
toℕ (lit (nat n)) = n
{-# CATCHALL #-}
toℕ _ = 0

open import Data.Product

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

record ⊤ {ℓ} : Set ℓ where
  constructor tt

-- Expressions of the form “⋯ , tt” may now be written “⟨ ⋯ ⟩”
infixr 5 ⟨ _⟩
⟨⟩ : ∀ {ℓ} → ⊤ {ℓ}
⟨⟩ = tt

⟨ : ∀ {ℓ} {S : Set ℓ} → S → S
⟨ s = s

_⟩ : ∀ {ℓ} {S : Set ℓ} → S → S × ⊤ {ℓ}
s ⟩ = s , tt

Context = λ ℓ → ℕ → Set ℓ

infix -1000 ‵_
‵_ : ∀ {ℓ} → Set ℓ → Context ℓ
‵ S = λ _ → S

End : ∀ {ℓ} → Context ℓ
End = ‵ ⊤

_>>=_ : ∀ {a b}
      → (Γ : Set a)  -- Main diference
      → (Γ → Context b)
      → Context (a ⊍ b)
(Γ >>= f) ℕ.zero  = Σ γ ∶ Γ • f γ 0
(Γ >>= f) (suc n) = (γ : Γ) → f γ n

Monoid : ∀ ℓ → Context (ℓsuc ℓ)
Monoid ℓ = do Carrier ← Set ℓ
              Id      ← Carrier
              _⊕_     ← (Carrier → Carrier → Carrier)
              leftId  ← ∀ {x : Carrier} → x ⊕ Id ≡ x
              rightId ← ∀ {x : Carrier} → Id ⊕ x ≡ x
              assoc   ← ∀ {x y z} → (x ⊕ y) ⊕ z  ≡  x ⊕ (y ⊕ z)
              End {ℓ}

DynamicSystem : Context (ℓsuc Level.zero)
DynamicSystem = do X ← Set
                   z ← X
                   s ← (X → X)
                   End {Level.zero}

-- Records with 𝓃-Parameters, 𝓃 : 0..3
A B C D : Set₁
A = DynamicSystem 0 -- Σ X ∶ Set  • Σ z ∶ X  • Σ s ∶ X → X  • ⊤
B = DynamicSystem 1 --  (X ∶ Set) → Σ z ∶ X  • Σ s ∶ X → X  • ⊤
C = DynamicSystem 2 --  (X ∶ Set)    (z ∶ X) → Σ s ∶ X → X  • ⊤
D = DynamicSystem 3 --  (X ∶ Set)    (z ∶ X) →  (s ∶ X → X) → ⊤

stablity : ∀ {n} →   DynamicSystem (3 + n)
                   ≡ DynamicSystem  3
stablity = refl

B-is-empty : ¬ B
B-is-empty b = proj₁( b ⊥)

𝒩₀ : DynamicSystem 0
𝒩₀ = ℕ , 0 , suc , tt

𝒩 : DynamicSystem 0
𝒩 = ⟨ ℕ , 0 , suc ⟩

B-on-ℕ : Set
B-on-ℕ = let X = ℕ in Σ z ∶ X  • Σ s ∶ (X → X)  • ⊤

ex : B-on-ℕ
ex = ⟨ 0 , suc ⟩

idτ : Set₁
idτ = ∀ (X : Set) (e : X) → X

id₁ : ∀ (X : Set) → Set
id₁ = λ (X : Set) → ((e : X) → X)

id₂ : ∀ (X : Set) (e : X) → Set
id₂ = λ (X : Set) (e : X) → X

Π→λ-helper : Term → Term
Π→λ-helper (pi  a b)         = lam visible b
Π→λ-helper (lam a (abs x y)) = lam a (abs x (Π→λ-helper y))
{-# CATCHALL #-}
Π→λ-helper x = x

macro
  Π→λ : Term → Term → TC Unit.⊤
  Π→λ tm goal = normalise tm >>=ₘ λ tm′ → unify (Π→λ-helper tm′) goal

_ : Π→λ idτ ≡ id₁
_ = refl

-- Too much yellow, sort constraints cannot be solved. It's okay.
-- _ : Π→λ (Π→λ idτ) ≡ id₂
-- _ = refl

_ : Π→λ (DynamicSystem 1) ≡ λ γ → Σ γ (λ _ → Σ ((x : γ) → γ) (λ _ → ⊤))
_ = refl

CC : ∀ (X : Set) (x : X) → Set
CC = Π→λ (Π→λ (DynamicSystem 2))   -- c.f., C above and C′ below.

waist-helper : ℕ → Term → Term
waist-helper zero t    = t
-- waist-helper (suc n) t = waist-helper n (Π→λ t)
waist-helper (suc n) t = waist-helper n (Π→λ-helper t)

macro
  _:waist_ : Term → Term → Term → TC Unit.⊤
  _:waist_ t 𝓃 goal =      normalise (t app 𝓃)
                      >>=ₘ λ t′ → unify (waist-helper (toℕ 𝓃) t′) goal

A′ : Set₁
B′ : ∀ (X : Set) → Set
C′ : ∀ (X : Set) (x : X) → Set
D′ : ∀ (X : Set) (x : X) (s : X → X) → Set

A′ = DynamicSystem :waist 0
B′ = DynamicSystem :waist 1
C′ = DynamicSystem :waist 2
D′ = DynamicSystem :waist 3

𝒩⁰ : A′
𝒩⁰ = ⟨ ℕ , 0 , suc ⟩

𝒩¹ : B′ ℕ
𝒩¹ = ⟨ 0 , suc ⟩

𝒩² : C′ ℕ 0
𝒩² = ⟨ suc ⟩

𝒩³ : D′ ℕ 0 suc
𝒩³ = ⟨⟩

Collection : ∀ ℓ → Context (ℓsuc ℓ)
Collection ℓ = do
  Elem    ← Set ℓ
  Carrier ← Set ℓ
  ∅       ← Carrier
  insert  ← (Elem → Carrier → Carrier)
  isEmpty ← (Carrier → Bool)
  insert-nonEmpty ← ∀ {e : Elem} {x : Carrier} → isEmpty (insert e x) ≡ false
  End {ℓ}

ListColl : {ℓ : Level} → Collection ℓ 1
ListColl E = ⟨ List E
             , []
             , _∷_ , (λ { [] → true; _ → false})
             , (λ {x} {x = x₁} → refl)
             ⟩

Collection₀ = Collection ℓ₀

ℕCollection = (Collection₀ :waist 2)
                ("Elem"    ≔ Digit)
                ("Carrier" ≔ ℕ)
--
-- i.e., (Collection₀ :waist 2) Digit ℕ

stack : ℕCollection
stack = ⟨ "empty stack" ≔ 0
        , "insert"      ≔ (λ d s → suc (10 * s + #→ℕ d))
        , "is-empty"    ≔ (λ { 0 → true; _ → false})
        -- Properties --
        , (λ {d : Digit} {s : ℕ} → refl {x = false})
        ⟩
