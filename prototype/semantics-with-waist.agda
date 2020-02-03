module semantics-with-waist where

open import Level renaming (_⊔_ to _⊍_; suc to ℓsuc; zero to ℓ₀)
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

record ⊤ {ℓ} : Set ℓ where
  constructor tt

-- Expressions of the form “⋯ , tt” may now be written “⟨ ⋯ ⟩”

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

𝒩₀ : DynamicSystem 0
𝒩₀ = ℕ , 0 , suc , tt

𝒩 : DynamicSystem 0
𝒩 = ⟨ ℕ , 0 , suc ⟩


