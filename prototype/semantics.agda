-- The .agda file is trangled from an org file.
module semantics where

open import Data.Product
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Level renaming (zero to ℓ₀; suc to ℓsuc; _⊔_ to _⊍_)

import Data.Nat  as ℕ
open import Data.Fin  as Fin using (Fin)
open import Data.Bool renaming (Bool to 𝔹)

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

record ⊤ {ℓ} : Set ℓ where
  constructor tt

Context = λ ℓ → Set ℓ

infixr 1 _>>=_ _>>_

_>>_ : ∀ {ℓ} → Context ℓ → Context ℓ → Context ℓ
p >> q = p ⊎ q

_>>=_ : ∀ {a ℓ}
      → (Γ : Context a)
      → (Γ → Context ℓ)
      → Context (a ⊍ ℓ)
Γ >>= f = (Σ γ ∶ Γ • f γ)
-- The new piece, f γ, is kept along with the old existing context via “γ ∶ Γ”.

End : ∀ {ℓ} → Context ℓ
End {ℓ} = ⊤ {ℓ}

PointedPF : (Ξ : Context (ℓsuc ℓ₀)) → Context (ℓsuc ℓ₀)
PointedPF Ξ = do Carrier ← Set
                 point   ← Carrier
                 Ξ

-- A record type --- Σ Set ∶ Carrier • Σ point ∶ Carrier • ⊤
PointedSet = PointedPF ⊤

-- An extended record type
-- Σ Set ∶ Carrier₁ • Σ point₁ ∶ Carrier₁ • (Σ Carrier₂ ∶ Set • Σ point₂ ∶ Carrier₁ • ⊤)
TwoPointedSets = PointedPF PointedSet

_PointedSets : ℕ → Set₁
zero  PointedSets = ⊤
suc n PointedSets = PointedPF (n PointedSets)

-- C-c C-n 4 PointedSets ⇒ Somewhat readable definition of the record!

example₁ : PointedSet
example₁ = ℕ , 0 , tt

example₂ : PointedSet
example₂ = Fin.Fin 3 , Fin.suc Fin.zero , tt

example₃ : TwoPointedSets
example₃ = 𝔹 , true , example₁
-- A pointed nat extended by a pointed bool, with particular choices for both.

TwoParameterPoints : ∀ {ℓ} (Ξ : Context ℓ) → Context ℓ
TwoParameterPoints {ℓ} Ξ = do one   ← Ξ
                              two   ← Ξ
                              End {ℓ}

-- C-c C-n TwoParameterPoints   ⇒   λ Ξ → Σ one ∶ Ξ • Σ two ∶ Ξ • ⊤

example₄ : TwoParameterPoints 𝔹
example₄ = false , false , tt  -- Obtained with C-c C-a

example₅ : TwoParameterPoints PointedSet
example₅ = example₁ , example₂ , tt

Magma : ∀ {ℓ} → Context ℓ → Context (ℓsuc ℓ)
Magma {ℓ} Ξ = do Carrier ← Set ℓ
                 _⊕_     ← (Carrier → Carrier → Carrier)
                 one     ← Carrier
                 two     ← Carrier
                 two ≡ one ⊕ one  -- ‘Defn’ of two

example₆ : Magma ⊤
example₆ = ℕ , ℕ._+_ , 4 , 8 , refl
