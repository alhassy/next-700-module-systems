-- [[Context Examples Header][Context Examples Header:1]]
-- Agda version 2.6.0.1
-- Standard library version 1.2

module Context_Examples where

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
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₘ_)
-- Context Examples Header:1 ends here

-- [[The Problems][The Problems:1]]
record DynamicSystem₀ : Set₁ where
  field
    State : Set
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

-- [[The Problems][The Problems:2]]
_ : Set₁
_ = DynamicSystem₀

_ : Π X ∶ Set • Set
_ = DynamicSystem₁

_ : Π X ∶ Set • Π x ∶ X • Set
_ = DynamicSystem₂
-- The Problems:2 ends here

-- [[The Problems][The Problems:3]]
id₀ : Set₁
id₀ = Π X ∶ Set • Π e ∶ X • X

id₁ : Π X ∶ Set • Set
id₁ = λ (X : Set) → Π e ∶ X • X

id₂ : Π X ∶ Set • Π e ∶ X • Set
id₂ = λ (X : Set) (e : X) → X
-- The Problems:3 ends here

-- [[The Problems][The Problems:4]]
data DSTerms₀ : Set where
  start : DSTerms₀
  next  : DSTerms₀ → DSTerms₀

data DSTerms₁ (State : Set) : Set where
  start : State → DSTerms₁ State
  next  : DSTerms₁ State → DSTerms₁ State

data DSTerms₂ (State : Set) (start : State) : Set where
  next : DSTerms₂ State start → DSTerms₂ State start
-- The Problems:4 ends here

-- [[The Problems][The Problems:5]]
_ : Set
_ = DSTerms₀

_ : Π X ∶ Set • Set
_ = DSTerms₁

_ : Π X ∶ Set • Π x ∶ X • Set
_ = DSTerms₂
-- The Problems:5 ends here

-- [[Monadic Notation][Monadic Notation:10]]
Monoid : ∀ ℓ → Context (ℓsuc ℓ)
Monoid ℓ = do Carrier ← Set ℓ
              _⊕_     ← (Carrier → Carrier → Carrier)
              Id      ← Carrier
              leftId  ← ∀ {x : Carrier} → x ⊕ Id ≡ x
              rightId ← ∀ {x : Carrier} → Id ⊕ x ≡ x
              assoc   ← ∀ {x y z} → (x ⊕ y) ⊕ z  ≡  x ⊕ (y ⊕ z)
              End {ℓ}
-- Monadic Notation:10 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:3]]
module termtype[Monoid]≅TreeSkeleton where
-- Free Datatypes from Theories:3 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:4]]
  𝕄 : Set
  𝕄 = termtype (Monoid ℓ₀ :waist 1)
  {- i.e., Fix (λ X → 𝟙      -- Id, nil leaf
                 ⊎ X × X × 𝟙 -- _⊕_, branch
                 ⊎ 𝟘         -- invariant leftId
                 ⊎ 𝟘         -- invariant rightId
                 ⊎ X × X × 𝟘 -- invariant assoc
                 ⊎ 𝟘)        -- the “End {ℓ}”
  -}

  -- Pattern synonyms for more compact presentation
  pattern emptyM      = μ (inj₂ (inj₁ tt))               -- : 𝕄
  pattern branchM l r = μ (inj₁ (l , r , tt))            -- : 𝕄 → 𝕄 → 𝕄
  pattern absurdM a   = μ (inj₂ (inj₂ (inj₂ (inj₂ a))))  -- absurd values of 𝟘

  data TreeSkeleton : Set where
    empty  : TreeSkeleton
    branch : TreeSkeleton → TreeSkeleton → TreeSkeleton
-- Free Datatypes from Theories:4 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:5]]
  to : 𝕄 → TreeSkeleton
  to emptyM        = empty
  to (branchM l r) = branch (to l) (to r)
  to (absurdM (inj₁ ()))
  to (absurdM (inj₂ ()))

  from : TreeSkeleton → 𝕄
  from empty        = emptyM
  from (branch l r) = branchM (from l) (from r)
-- Free Datatypes from Theories:5 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:6]]
  from∘to : ∀ m → from (to m) ≡ m
  from∘to emptyM        = refl
  from∘to (branchM l r) = cong₂ branchM (from∘to l) (from∘to r)
  from∘to (absurdM (inj₁ ()))
  from∘to (absurdM (inj₂ ()))

  to∘from : ∀ t → to (from t) ≡ t
  to∘from empty        = refl
  to∘from (branch l r) = cong₂ branch (to∘from l) (to∘from r)
-- Free Datatypes from Theories:6 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:7]]
module termtype[Collection]≅List where
-- Free Datatypes from Theories:7 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:8]]
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
-- Free Datatypes from Theories:8 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:9]]
  to : ∀ {E} → ℂ E → List E
  to (e :: es) = e ∷ to es
  to ∅         = []
-- Free Datatypes from Theories:9 ends here

-- [[Free Datatypes from Theories][Free Datatypes from Theories:10]]
  from : ∀ {E} → List E → ℂ E
  from []       = ∅
  from (x ∷ xs) = x :: from xs

  to∘from : ∀ {E} (xs : List E) → to (from xs) ≡ xs
  to∘from []       = refl
  to∘from (x ∷ xs) = cong (x ∷_) (to∘from xs)

  from∘to : ∀ {E} (e : ℂ E) → from (to e) ≡ e
  from∘to (e :: es) = cong (e ::_) (from∘to es)
  from∘to ∅         = refl
-- Free Datatypes from Theories:10 ends here

-- [[DynamicSystem Context][DynamicSystem Context:1]]
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

_ : A ≡ (Σ X ∶ Set  • Σ z ∶ X  • Σ s ∶ (X → X)  • ⊤) ; _ = refl
_ : B ≡ (Π X ∶ Set  • Σ z ∶ X  • Σ s ∶ (X → X)  • ⊤) ; _ = refl
_ : C ≡ (Π X ∶ Set  • Π z ∶ X  • Σ s ∶ (X → X)  • ⊤) ; _ = refl
_ : D ≡ (Π X ∶ Set  • Π z ∶ X  • Π s ∶ (X → X)  • ⊤) ; _ = refl

stability : ∀ {n} →   DynamicSystem (3 + n)
                   ≡ DynamicSystem  3
stability = refl

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
-- DynamicSystem Context:1 ends here

-- [[~idᵢ₊₁ ≈ Π→λ idᵢ~][~idᵢ₊₁ ≈ Π→λ idᵢ~:1]]
_ : id₁ ≡ Π→λ id₀
_ = refl

_ : id₂ ≡ Π→λ id₁
_ = refl
-- ~idᵢ₊₁ ≈ Π→λ idᵢ~:1 ends here

-- [[DynamicSystem :waist 𝒾][DynamicSystem :waist 𝒾:1]]
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
-- DynamicSystem :waist 𝒾:1 ends here

-- [[DynamicSystem :waist 𝒾][DynamicSystem :waist 𝒾:2]]
_ : DynamicSystem 0 ≡ DynamicSystem :waist 0
_ = refl
-- DynamicSystem :waist 𝒾:2 ends here

-- [[Stage 1: Records][Stage 1: Records:1]]
D₁ = DynamicSystem 0

1-records : D₁ ≡ (Σ X ∶ Set • Σ z ∶ X • Σ s ∶ (X → X) • ⊤)
1-records = refl
-- Stage 1: Records:1 ends here

-- [[Stage 2: Parameterised Records][Stage 2: Parameterised Records:1]]
D₂ = DynamicSystem :waist 1

2-funcs : D₂ ≡ (λ (X : Set) → Σ z ∶ X • Σ s ∶ (X → X) • ⊤)
2-funcs = refl
-- Stage 2: Parameterised Records:1 ends here

-- [[Stage 3: Sources][Stage 3: Sources:5]]
D₃ = sources D₂

3-sources : D₃ ≡ λ (X : Set) → Σ z ∶ 𝟙 • Σ s ∶ X • 𝟘
3-sources = refl
-- Stage 3: Sources:5 ends here

-- [[Stage 4: ~Σ→⊎~ --Replacing Products with Sums][Stage 4: ~Σ→⊎~ --Replacing Products with Sums:3]]
D₄ = Σ→⊎ D₃

4-unions : D₄ ≡ λ X → 𝟙 ⊎ X ⊎ 𝟘
4-unions = refl
-- Stage 4: ~Σ→⊎~ --Replacing Products with Sums:3 ends here

-- [[Stage 5: Fixpoint and proof that ~𝔻 ≅ ℕ~][Stage 5: Fixpoint and proof that ~𝔻 ≅ ℕ~:2]]
module termtype[DynamicSystem]≅ℕ where

  𝔻 = Fix D₄

  -- Pattern synonyms for more compact presentation
  pattern zeroD  = μ (inj₁ tt)       -- : 𝔻
  pattern sucD e = μ (inj₂ (inj₁ e)) -- : 𝔻 → 𝔻

  to : 𝔻 → ℕ
  to zeroD    = 0
  to (sucD x) = suc (to x)

  from : ℕ → 𝔻
  from zero    = zeroD
  from (suc n) = sucD (from n)

  to∘from : ∀ n → to (from n) ≡ n
  to∘from zero    = refl
  to∘from (suc n) = cong suc (to∘from n)

  from∘to : ∀ d → from (to d) ≡ d
  from∘to zeroD    = refl
  from∘to (sucD x) = cong sucD (from∘to x)
-- Stage 5: Fixpoint and proof that ~𝔻 ≅ ℕ~:2 ends here

-- [[~termtype~ and ~Inj~ macros][~termtype~ and ~Inj~ macros:3]]
𝔻 = termtype (DynamicSystem :waist 1)
-- ~termtype~ and ~Inj~ macros:3 ends here

-- [[~termtype~ and ~Inj~ macros][~termtype~ and ~Inj~ macros:4]]
startD : 𝔻
startD = Inj 0 (tt {ℓ₀})

nextD′ : 𝔻 → 𝔻
nextD′ d = Inj 1 d
-- ~termtype~ and ~Inj~ macros:4 ends here

-- [[Example: Graphs in Two Ways][Example: Graphs in Two Ways:2]]
record Graph₀ : Set₁ where
  constructor ⟨_,_⟩₀
  field
    Vertex : Set
    Edges : Vertex → Vertex → Set

open Graph₀

comap₀ : {A B : Set}
       → (f : A → B)
       → (Σ G ∶ Graph₀ • Vertex G ≡ B)
       → (Σ H ∶ Graph₀ • Vertex H ≡ A)
comap₀ {A} f (G , refl) = ⟨ A , (λ x y → Edges G (f x) (f y)) ⟩₀ , refl
-- Example: Graphs in Two Ways:2 ends here

-- [[Example: Graphs in Two Ways][Example: Graphs in Two Ways:3]]
record Graph₁ (Vertex : Set) : Set₁ where
  constructor ⟨_⟩₁
  field
    Edges : Vertex → Vertex → Set

comap₁ : {A B : Set}
       → (f : A → B)
       → Graph₁ B
       → Graph₁ A
comap₁ f ⟨ edges ⟩₁ = ⟨ (λ x y → edges (f x) (f y)) ⟩₁
-- Example: Graphs in Two Ways:3 ends here

-- [[Example: Graphs with Delayed Unbundling][Example: Graphs with Delayed Unbundling:1]]
Graph  : Context ℓ₁
Graph  = do Vertex ← Set
            Edges  ← (Vertex → Vertex → Set)
            End {ℓ₀}
-- Example: Graphs with Delayed Unbundling:1 ends here

-- [[Example: Graphs with Delayed Unbundling][Example: Graphs with Delayed Unbundling:2]]
pattern ⟨_,_⟩ V E = (V , E , tt)

comap₀′ : ∀ {A B : Set}
      → (f : A → B)
      → Σ G ∶ Graph :kind ‵record • Field 0 G ≡ B
      → Σ G ∶ Graph :kind ‵record • Field 0 G ≡ A
comap₀′ {A} {B} f (⟨ .B , edgs ⟩ , refl) = (A , (λ a₁ a₂ → edgs (f a₁) (f a₂)) , tt) , refl
-- Example: Graphs with Delayed Unbundling:2 ends here

-- [[Example: Graphs with Delayed Unbundling][Example: Graphs with Delayed Unbundling:3]]
pattern ⟨_⟩¹ E = (E , tt)

-- Way better and less awkward!
comap′ : ∀ {A B : Set}
     → (f : A → B)
     → (Graph :kind ‵typeclass) B
     → (Graph :kind ‵typeclass) A
comap′ f ⟨ edgs ⟩¹ = ⟨ (λ a₁ a₂ → edgs (f a₁) (f a₂)) ⟩¹
-- Example: Graphs with Delayed Unbundling:3 ends here
