-- 
-- The Next 700 Module Systems (•̀ᴗ•́)و Musa Al-hassy ⟨2021-01-22 Friday 16:25:19⟩
-- 
-- This file was mechanically generated from a literate program.
-- Namely, my PhD thesis on ‘do-it-yourself module systems for Agda’.
-- 
-- https://alhassy.github.io/next-700-module-systems/thesis.pdf
-- 
-- There are “[[backward][references]]” to the corresponding expository text.
-- 
-- Agda version 2.6.1.2; Standard library version 1.2

open import Level renaming (_⊔_ to _⊍_; suc to ℓsuc; zero to ℓ₀)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Nat
open import Data.Fin  as Fin using (Fin)
open import Data.Maybe  hiding (_>>=_)

open import Data.Bool using (Bool ; true ; false)
open import Data.List as List using (List ; [] ; _∷_ ; _∷ʳ_; sum)

import Data.Unit as Unit

-- The map-Args of Reflection is deprecated, and it is advised to use the map-Args
-- within Reflection.Argument.
open import Reflection hiding (name; Type; map-Arg;  map-Args) renaming (_>>=_ to _>>=ₜₑᵣₘ_)
open import Reflection.Argument using (map-Args) renaming (map to map-Arg)

ℓ₁   = Level.suc ℓ₀

open import Data.Empty using (⊥)
open import Data.Sum
open import Data.Product
open import Function using (_∘_)

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

Π∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Π∶• A B = (x : A) → B x

infix -666 Π∶•
syntax Π∶• A (λ x → B) = Π x ∶ A • B

record 𝟙 {ℓ} : Set ℓ where
  constructor tt

𝟘 = ⊥

-- [[Single argument application][Single argument application:1]]
_app_ : Term → Term → Term
(def f args) app arg' = def f (args ∷ʳ arg (arg-info visible relevant) arg')
(con f args) app arg' = con f (args ∷ʳ arg (arg-info visible relevant) arg')
{-# CATCHALL #-}
tm app arg' = tm
-- Single argument application:1 ends here

-- [[Reify ℕ term encodings as ℕ values][Reify ℕ term encodings as ℕ values:1]]
toℕ : Term → ℕ
toℕ (lit (nat n)) = n
{-# CATCHALL #-}
toℕ _ = 0
-- Reify ℕ term encodings as ℕ values:1 ends here

{- Type annotation -}
syntax has A a = a ∶ A

has : ∀ {ℓ} (A : Set ℓ) (a : A) → A
has A a = a

-- From: https://alhassy.github.io/PathCat.html  § Imports
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_ ; _≡_)
module _ {i} {S : Set i} where
    open import Relation.Binary.Reasoning.Setoid (≡.setoid S) public

open import Agda.Builtin.String

defn-chasing : ∀ {i} {A : Set i} (x : A) → String → A → A
defn-chasing x reason supposedly-x-again = supposedly-x-again

syntax defn-chasing x reason xish = x ≡⟨ reason ⟩' xish

infixl 3 defn-chasing

{- “Contexts” are exposure-indexed types -}
Context = λ ℓ → ℕ → Set ℓ

{- Every type can be used as a context -}
‵_ : ∀ {ℓ} → Set ℓ → Context ℓ
‵ S = λ _ → S

{- The “empty context” is the unit type -}
End : ∀ {ℓ} → Context ℓ
End {ℓ} = ‵ 𝟙 {ℓ}

_>>=_ : ∀ {a b}
      → (Γ : Set a)  -- Main difference
      → (Γ → Context b)
      → Context (a ⊍ b)
(Γ >>= f) zero    = Σ γ ∶ Γ • f γ 0
(Γ >>= f) (suc n) = Π γ ∶ Γ • f γ n

Π→λ-type : Term → Term
Π→λ-type (pi a (abs x b)) = pi a  (abs x (Π→λ-type b))
Π→λ-type x = unknown

Π→λ-helper : Term → Term
Π→λ-helper (pi a (abs x b)) = lam visible (abs x (Π→λ-helper b))
Π→λ-helper x = x

macro
  Π→λ : Term → Term → TC Unit.⊤
  Π→λ tm goal =  normalise tm
                 >>=ₜₑᵣₘ λ tm' → checkType goal (Π→λ-type tm')
                 >>=ₜₑᵣₘ λ _ →  unify goal (Π→λ-helper tm')

{- ρ :waist n  ≡  Π→λ (ρ n)  -}
macro
  _:waist_ : (pkg : Term) (height : Term) (goal : Term) → TC Unit.⊤
  _:waist_ pkg n goal = normalise (pkg app n)
                        >>=ₜₑᵣₘ λ ρ → checkType goal (Π→λ-type ρ)
                        >>=ₜₑᵣₘ λ _ → unify goal (Π→λ-helper ρ)

-- Expressions of the form “⋯ , tt” may now be written “⟨ ⋯ ⟩”
infixr 5 ⟨ _⟩
⟨⟩ : ∀ {ℓ} → 𝟙 {ℓ}
⟨⟩ = tt

⟨ : ∀ {ℓ} {S : Set ℓ} → S → S
⟨ s = s

_⟩ : ∀ {ℓ} {S : Set ℓ} → S → S × (𝟙 {ℓ})
s ⟩ = s , tt

-- The source of a type, not an arbitrary term.
-- E.g., sources (Σ x ∶ τ • body) = Σ x ∶ sourcesₜ τ • sources body
sourcesₜ : Term → Term

{- “Π {a ∶ A} • Ba”  ↦  𝟘 -}
sourcesₜ (pi (arg (arg-info hidden _) A) _) = quoteTerm 𝟘

{-  “Π a ∶ A • Π b ∶ Ba • C a b” ↦ “Σ a ∶ A • Σ b ∶ B a • sourcesₜ (C a b)”  -}
sourcesₜ (pi (arg a A) (abs “a” (pi (arg b Ba) (abs “b” Cab)))) =
  def (quote Σ) (vArg A
                ∷ vArg (lam visible (abs “a”
                   (def (quote Σ)
                          (vArg Ba
                         ∷ vArg (lam visible (abs “b” (sourcesₜ Cab)))
                         ∷ []))))
                ∷ [])

{-  “Π a ∶ A • Ba” ↦ “A” provided Ba does not begin with a Π  -}
sourcesₜ (pi (arg a A) (abs “a” Ba)) = A

{- All other non function types have an empty source; since X ≅ (𝟙 → X) -}
sourcesₜ _ = quoteTerm (𝟙 {ℓ₀})

{-# TERMINATING #-} -- Termination via structural smaller arguments is not clear due to the call to List.map
sourcesₜₑᵣₘ : Term → Term

sourcesₜₑᵣₘ (pi a b) = sourcesₜ (pi a b)
{- “Σ x ∶ τ • Bx” ↦  “Σ x ∶ sourcesₜ τ • sources Bx” -}
sourcesₜₑᵣₘ (def (quote Σ) (ℓ₁ ∷ ℓ₂ ∷ τ ∷ body))
    = def (quote Σ) (ℓ₁ ∷ ℓ₂ ∷ map-Arg sourcesₜ τ ∷ List.map (map-Arg sourcesₜₑᵣₘ) body)

{- This function introduces 𝟙s, so let's drop any old occurances a la 𝟘. -}
sourcesₜₑᵣₘ (def (quote 𝟙) _) = def (quote 𝟘) []

-- TODO: Maybe we do not need these cases.
sourcesₜₑᵣₘ (lam v (abs s x))     = lam v (abs s (sourcesₜₑᵣₘ x))
sourcesₜₑᵣₘ (var x args) = var x (List.map (map-Arg sourcesₜₑᵣₘ) args)
sourcesₜₑᵣₘ (con c args) = con c (List.map (map-Arg sourcesₜₑᵣₘ) args)
sourcesₜₑᵣₘ (def f args) = def f (List.map (map-Arg sourcesₜₑᵣₘ) args)
sourcesₜₑᵣₘ (pat-lam cs args) =  pat-lam cs (List.map (map-Arg sourcesₜₑᵣₘ) args)

-- sort, lit, meta, unknown
sourcesₜₑᵣₘ t = t

macro
  sources : Term → Term → TC Unit.⊤
  sources tm goal = normalise tm >>=ₜₑᵣₘ λ tm' → unify (sourcesₜₑᵣₘ tm') goal

arg-term : ∀ {ℓ} {A : Set ℓ} → (Term → A) → Arg Term → A
arg-term f (arg i x) = f x

{-# TERMINATING #-}
lengthₜ : Term → ℕ
lengthₜ (var x args)      = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (con c args)      = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (def f args)      = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (lam v (abs s x)) = 1 + lengthₜ x
lengthₜ (pat-lam cs args) = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (pi X (abs b Bx)) = 1 + lengthₜ Bx
{-# CATCHALL #-}
-- sort, lit, meta, unknown
lengthₜ t = 0
-- The Length of a Term:1 ends here

-- [[The Length of a Term][The Length of a Term:2]]
_ : lengthₜ (quoteTerm (Σ x ∶ ℕ • x ≡ x)) ≡ 10
_ = refl

--
var-dec₀ : (fuel : ℕ) → Term → Term
var-dec₀ zero t  = t
-- Let's use an “impossible” term.
var-dec₀ (suc n) (var zero args)      = def (quote 𝟘) []
var-dec₀ (suc n) (var (suc x) args)   = var x args
var-dec₀ (suc n) (con c args)         = con c (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (def f args)         = def f (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (lam v (abs s x))    = lam v (abs s (var-dec₀ n x))
var-dec₀ (suc n) (pat-lam cs args)    = pat-lam cs (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (pi (arg a A) (abs b Ba)) = pi (arg a (var-dec₀ n A)) (abs b (var-dec₀ n Ba))
-- var-dec₀ (suc n) (Π[ s ∶ arg i A ] B) = Π[ s ∶ arg i (var-dec₀ n A) ] var-dec₀ n B
{-# CATCHALL #-}
-- sort, lit, meta, unknown
var-dec₀ n t = t

var-dec : Term → Term
var-dec t = var-dec₀ (lengthₜ t) t

{-# TERMINATING #-}
Σ→⊎₀ : Term → Term

{-  “Σ a ∶ A • Ba” ↦ “A ⊎ B” where ‘B’ is ‘Ba’ with no reference to ‘a’  -}
Σ→⊎₀ (def (quote Σ) (𝒽₁ ∷ 𝒽₀ ∷ arg i A ∷ arg i₁ (lam v (abs s x)) ∷ []))
  =  def (quote _⊎_) (𝒽₁ ∷ 𝒽₀ ∷ arg i A ∷ vArg (Σ→⊎₀ (var-dec x)) ∷ [])

-- Interpret “End” in do-notation to be an empty, impossible, constructor.
-- See the unit tests above ;-)
-- For some reason, the inclusion of this caluse obscures structural termination.
Σ→⊎₀ (def (quote 𝟙) _) = def (quote 𝟘) []

 -- Walk under λ's and Π's.
Σ→⊎₀ (lam v (abs s x)) = lam v (abs s (Σ→⊎₀ x))
Σ→⊎₀ (pi A (abs a Ba)) = pi A (abs a (Σ→⊎₀ Ba))
Σ→⊎₀ t = t

macro
  Σ→⊎ : Term → Term → TC Unit.⊤
  Σ→⊎ tm goal = normalise tm >>=ₜₑᵣₘ λ tm' → unify (Σ→⊎₀ tm') goal

{-# NO_POSITIVITY_CHECK #-}
data Fix {ℓ} (F : Set ℓ → Set ℓ) : Set ℓ where
  μ : F (Fix F) → Fix F

macro
  termtype : Term → Term → TC Unit.⊤
  termtype tm goal =
                normalise tm
           >>=ₜₑᵣₘ λ tm' → unify goal (def (quote Fix) ((vArg (Σ→⊎₀ (sourcesₜₑᵣₘ tm'))) ∷ []))

-- 𝒾-th injection:  (inj₂ ∘ ⋯ ∘ inj₂) ∘ inj₁
Inj₀ : ℕ → Term → Term
Inj₀ zero c    = con (quote inj₁) (arg (arg-info visible relevant) c ∷ [])
Inj₀ (suc n) c = con (quote inj₂) (vArg (Inj₀ n c) ∷ [])

macro
  Inj : ℕ → Term → Term → TC Unit.⊤
  Inj n t goal = unify goal ((con (quote μ) []) app (Inj₀ n t))
