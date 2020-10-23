-- [[file:thesis.org::*Context Examples Header][Context Examples Header:1]]
-- Agda version 2.6.0.1
-- Standard library version 1.2

module Examples where

open import Context

open import Data.Product
open import Level renaming (zero to ℓ₀; suc to ℓsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Relation.Nullary
open import Data.Nat
open import Function using (id)
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Sum

open import Data.List
import Data.Unit as Unit
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₜₑᵣₘ_)
-- Context Examples Header:1 ends here

-- [[file:thesis.org::*The Problems][The Problems:1]]
record DynamicSystem₀ : Set₁ where
  field
    State  : Set
    start  : State
    next   : State → State

record DynamicSystem₁ (State : Set) : Set where
  field
    start : State
    next  : State → State

record DynamicSystem₂ (State : Set) (start : State) : Set where
  field
    next : State → State
-- The Problems:1 ends here

-- [[file:thesis.org::*The Problems][The Problems:2]]
_ : Set₁
_ = DynamicSystem₀

_ : Π X ∶ Set • Set
_ = DynamicSystem₁

_ : Π X ∶ Set • Π x ∶ X • Set
_ = DynamicSystem₂
-- The Problems:2 ends here

-- [[file:thesis.org::*The Problems][The Problems:3]]
idτ₀ : Set₁
idτ₀ = Π X ∶ Set • Π e ∶ X • X

idτ₁ : Π X ∶ Set • Set
idτ₁ = λ (X : Set) → Π e ∶ X • X

idτ₂ : Π X ∶ Set • Π e ∶ X • Set
idτ₂ = λ (X : Set) (e : X) → X

{- Surprisingly, the latter is derivable from the former -}
_ : idτ₂ ≡ Π→λ idτ₀
_ = refl

{- The relationship with idτ₁ is clarified later when we get to _:waist_ -}
-- The Problems:3 ends here

-- [[file:thesis.org::*Monadic Notation][Monadic Notation:2]]
DynamicSystem : Context ℓ₁
DynamicSystem = do State ← Set
                   start ← State
                   next  ← (State → State)
                   End {ℓ₀}
-- Monadic Notation:2 ends here

-- [[file:thesis.org::*Monadic Notation][Monadic Notation:7]]
𝒩₀ : DynamicSystem 0   {- See the above elaborations  -}
𝒩₀ = ℕ , 0 , suc , tt

-- 𝒩₁ : DynamicSystem 1
-- 𝒩₁ = λ State → ??? {- Impossible to complete if “State” is empty! -}

{- ‘Instantiaing’ State to be ℕ in “DynamicSystem 1” -}
𝒩₁′ : let State = ℕ in Σ start ∶ State  • Σ s ∶ (State → State)  • 𝟙 {ℓ₀}
𝒩₁′ = 0 , suc , tt
-- Monadic Notation:7 ends here

-- [[file:thesis.org::*Monadic Notation][Monadic Notation:10]]
_ = Π→λ (DynamicSystem 2)
  ≡⟨" Definition of DynamicSystem at exposure level 2 "⟩′
    Π→λ (Π X ∶ Set • Π s ∶ X • Σ n ∶ (X → X)  • 𝟙 {ℓ₀})
  ≡⟨" Definition of Π→λ; replace a ‘Π’ by a ‘λ’ "⟩′
    (λ (X : Set) → Π→λ (Π s ∶ X • Σ n ∶ (X → X)  • 𝟙 {ℓ₀}))
  ≡⟨" Definition of Π→λ; replace a ‘Π’ by a ‘λ’ "⟩′
    (λ (X : Set) → λ (s : X) → Π→λ (Σ n ∶ (X → X)  • 𝟙 {ℓ₀}))
  ≡⟨" Next symbol is not a ‘Π’, so Π→λ stops "⟩′
    λ (X : Set) → λ (s : X) → Σ n ∶ (X → X)  • 𝟙 {ℓ₀}
-- Monadic Notation:10 ends here

-- [[file:thesis.org::*Monadic Notation][Monadic Notation:15]]
𝒩⁰ : DynamicSystem :waist 0
𝒩⁰ = ⟨ ℕ , 0 , suc ⟩

𝒩¹ : (DynamicSystem :waist 1) ℕ
𝒩¹ = ⟨ 0 , suc ⟩

𝒩² : (DynamicSystem :waist 2) ℕ 0
𝒩² = ⟨ suc ⟩

𝒩³ : (DynamicSystem :waist 3) ℕ 0 suc
𝒩³ = ⟨⟩
-- Monadic Notation:15 ends here

-- [[file:thesis.org::*Monadic Notation][Monadic Notation:16]]
Monoid : ∀ ℓ → Context (ℓsuc ℓ)
Monoid ℓ = do Carrier ← Set ℓ
              _⊕_     ← (Carrier → Carrier → Carrier)
              Id      ← Carrier
              leftId  ← ∀ {x : Carrier} → x ⊕ Id ≡ x
              rightId ← ∀ {x : Carrier} → Id ⊕ x ≡ x
              assoc   ← ∀ {x y z} → (x ⊕ y) ⊕ z  ≡  x ⊕ (y ⊕ z)
              End {ℓ}
-- Monadic Notation:16 ends here

-- [[file:thesis.org::*Stage 1: Records][Stage 1: Records:1]]
D₁ = DynamicSystem 0

1-records : D₁ ≡ (Σ X ∶ Set • Σ z ∶ X • Σ s ∶ (X → X) • 𝟙 {ℓ₀})
1-records = refl
-- Stage 1: Records:1 ends here

-- [[file:thesis.org::*Stage 2: Parameterised Records][Stage 2: Parameterised Records:1]]
D₂ = DynamicSystem :waist 1

2-funcs : D₂ ≡ (λ (X : Set) → Σ z ∶ X • Σ s ∶ (X → X) • 𝟙 {ℓ₀})
2-funcs = refl
-- Stage 2: Parameterised Records:1 ends here

-- [[file:thesis.org::*Stage 3: Sources][Stage 3: Sources:1]]
_ : sources (𝔹 → ℕ) ≡ 𝔹
_ = refl

_ : sources (Σ f ∶ (ℕ → 𝔹) • Set) ≡ (Σ x ∶ ℕ • Set)
_ = refl

_ : sources (Σ f ∶ (ℕ → Set → 𝔹 → ℕ) • 1 ≡ 1) ≡ (Σ x ∶ (ℕ × Set × 𝔹) • 1 ≡ 1)
_ = refl

_ : ∀ {ℓ} → sources (𝟙 {ℓ}) ≡ 𝟘
_ = refl

_ = (sources (∀ {x : ℕ} → ℕ)) ≡ 𝟘
_ = refl {ℓ₁} {Set} {𝟘}
-- Stage 3: Sources:1 ends here

-- [[file:thesis.org::*Stage 3: Sources][Stage 3: Sources:2]]
D₃ = sources D₂

3-sources : D₃ ≡ λ (X : Set) → Σ z ∶ 𝟙 • Σ s ∶ X • 𝟘
3-sources = refl
-- Stage 3: Sources:2 ends here

-- [[file:thesis.org::*Stage 4: ~Σ→⊎~ --Replacing Products with Sums][Stage 4: ~Σ→⊎~ --Replacing Products with Sums:1]]
_ : Σ→⊎ (Π S ∶ Set • (S → S)) ≡ (Π S ∶ Set • (S → S))
_ = refl

_ : Σ→⊎ (Π S ∶ Set • Σ n ∶ S • S) ≡ (Π S ∶ Set • S ⊎ S)
_ = refl

_ : Σ→⊎ (λ (S : Set) → Σ n ∶ S • S) ≡ λ S → S ⊎ S
_ = refl

_ : Σ→⊎ (Π S ∶ Set • Σ s ∶ S • Σ n ∶ (S → S) • 𝟙 {ℓ₀}) ≡ (Π S ∶ Set • S ⊎ (S → S) ⊎ 𝟘)
_ = refl

_ : Σ→⊎ (λ (S : Set) → Σ s ∶ S • Σ n ∶ (S → S) • 𝟙 {ℓ₀}) ≡ λ S → S ⊎ (S → S) ⊎ 𝟘
_ = refl
-- Stage 4: ~Σ→⊎~ --Replacing Products with Sums:1 ends here

-- [[file:thesis.org::*Stage 4: ~Σ→⊎~ --Replacing Products with Sums][Stage 4: ~Σ→⊎~ --Replacing Products with Sums:4]]
D₄ = Σ→⊎ D₃

4-unions : D₄ ≡ λ X → 𝟙 ⊎ X ⊎ 𝟘
4-unions = refl
-- Stage 4: ~Σ→⊎~ --Replacing Products with Sums:4 ends here

-- [[file:thesis.org::*Instructive Example: 𝔻 ≅ ℕ][Instructive Example: 𝔻 ≅ ℕ:3]]
module free-dynamical-system where

    𝔻 = termtype (DynamicSystem :waist 1)

    -- Pattern synonyms for more compact presentation
    pattern startD  = μ (inj₁ tt)       -- : 𝔻
    pattern nextD e = μ (inj₂ (inj₁ e)) -- : 𝔻 → 𝔻

    to : 𝔻 → ℕ
    to startD    = 0
    to (nextD x) = suc (to x)

    from : ℕ → 𝔻
    from zero    = startD
    from (suc n) = nextD (from n)
-- Instructive Example: 𝔻 ≅ ℕ:3 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:2]]
module termtype[Monoid]≅TreeSkeleton where
-- Free Datatypes from Theories:2 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:3]]
  𝕄 : Set
  𝕄 = termtype (Monoid ℓ₀ :waist 1)

  that-is : 𝕄 ≡ Fix (λ X → X × X × 𝟙 -- _⊕_, branch
                          ⊎ 𝟙        -- Id, nil leaf
                          ⊎ 𝟘        -- invariant leftId
                          ⊎ 𝟘        -- invariant rightId
                          ⊎ 𝟘        -- invariant assoc
                          ⊎ 𝟘)       --  the “End {ℓ}”
  that-is = refl

  -- Pattern synonyms for more compact presentation
  pattern emptyM      = μ (inj₂ (inj₁ tt))              -- : 𝕄
  pattern branchM l r = μ (inj₁ (l , r , tt))           -- : 𝕄 → 𝕄 → 𝕄
  pattern absurdM a   = μ (inj₂ (inj₂ (inj₂ (inj₂ a)))) -- absurd 𝟘-values

  data TreeSkeleton : Set where
    empty  : TreeSkeleton
    branch : TreeSkeleton → TreeSkeleton → TreeSkeleton
-- Free Datatypes from Theories:3 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:4]]
  to : 𝕄 → TreeSkeleton
  to emptyM        = empty
  to (branchM l r) = branch (to l) (to r)
  to (absurdM (inj₁ ()))
  to (absurdM (inj₂ ()))

  from : TreeSkeleton → 𝕄
  from empty        = emptyM
  from (branch l r) = branchM (from l) (from r)
-- Free Datatypes from Theories:4 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:5]]
  from∘to : ∀ m → from (to m) ≡ m
  from∘to emptyM        = refl
  from∘to (branchM l r) = cong₂ branchM (from∘to l) (from∘to r)
  from∘to (absurdM (inj₁ ()))
  from∘to (absurdM (inj₂ ()))

  to∘from : ∀ t → to (from t) ≡ t
  to∘from empty        = refl
  to∘from (branch l r) = cong₂ branch (to∘from l) (to∘from r)
-- Free Datatypes from Theories:5 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:6]]
module termtype[Collection]≅List where
-- Free Datatypes from Theories:6 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:7]]
  Collection : ∀ ℓ → Context (ℓsuc ℓ)
  Collection ℓ = do Elem    ← Set ℓ
                    Carrier ← Set ℓ
                    insert  ← (Elem → Carrier → Carrier)
                    ∅       ← Carrier
                    End {ℓ}

  ℂ : Set → Set
  ℂ Elem = termtype ((Collection ℓ₀ :waist 2) Elem)

  pattern _::_ x xs = μ (inj₁ (x , xs , tt))
  pattern  ∅        = μ (inj₂ (inj₁ tt))
-- Free Datatypes from Theories:7 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:8]]
  to : ∀ {E} → ℂ E → List E
  to (e :: es) = e ∷ to es
  to ∅         = []
-- Free Datatypes from Theories:8 ends here

-- [[file:thesis.org::*Free Datatypes from Theories][Free Datatypes from Theories:9]]
  from : ∀ {E} → List E → ℂ E
  from []       = ∅
  from (x ∷ xs) = x :: from xs

  to∘from : ∀ {E} (xs : List E) → to (from xs) ≡ xs
  to∘from []       = refl
  to∘from (x ∷ xs) = cong (x ∷_) (to∘from xs)

  from∘to : ∀ {E} (e : ℂ E) → from (to e) ≡ e
  from∘to (e :: es) = cong (e ::_) (from∘to es)
  from∘to ∅         = refl
-- Free Datatypes from Theories:9 ends here
