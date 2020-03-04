-- [[Appendices][Appendices:1]]
-- Agda version 2.6.0.1
-- Standard library version 1.2

module Context where
-- Appendices:1 ends here

-- [[Imports][Imports:1]]
open import Level renaming (_⊔_ to _⊍_; suc to ℓsuc; zero to ℓ₀)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Nat
open import Data.Fin  as Fin using (Fin)
open import Data.Maybe  hiding (_>>=_)

open import Data.Bool using (Bool ; true ; false)
open import Data.List as List using (List ; [] ; _∷_ ; _∷ʳ_; sum)

ℓ₁   = Level.suc ℓ₀
-- Imports:1 ends here

-- [[Quantifiers Π∶•/Σ∶• and Products/Sums][Quantifiers Π∶•/Σ∶• and Products/Sums:1]]
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

record ⊤ {ℓ} : Set ℓ where
  constructor tt

𝟙 = ⊤ {ℓ₀}
𝟘 = ⊥
-- Quantifiers Π∶•/Σ∶• and Products/Sums:1 ends here

-- [[Reflection][Reflection:1]]
import Data.Unit as Unit
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₘ_)
-- Reflection:1 ends here

-- [[Single argument application][Single argument application:1]]
_app_ : Term → Term → Term
(def f args) app arg′ = def f (args ∷ʳ arg (arg-info visible relevant) arg′)
(con f args) app arg′ = con f (args ∷ʳ arg (arg-info visible relevant) arg′)
{-# CATCHALL #-}
tm app arg′ = tm
-- Single argument application:1 ends here

-- [[Reify ℕ term encodings as ℕ values][Reify ℕ term encodings as ℕ values:1]]
toℕ : Term → ℕ
toℕ (lit (nat n)) = n
{-# CATCHALL #-}
toℕ _ = 0
-- Reify ℕ term encodings as ℕ values:1 ends here

-- [[The Length of a Term][The Length of a Term:1]]
arg-term : ∀ {ℓ} {A : Set ℓ} → (Term → A) → Arg Term → A
arg-term f (arg i x) = f x

{-# TERMINATING #-}
lengthₜ : Term → ℕ
lengthₜ (var x args)      = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (con c args)      = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (def f args)      = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (lam v (abs s x)) = 1 + lengthₜ x
lengthₜ (pat-lam cs args) = 1 + sum (List.map (arg-term lengthₜ ) args)
lengthₜ (Π[ x ∶ A ] Bx)   = 1 + lengthₜ Bx
{-# CATCHALL #-}
-- sort, lit, meta, unknown
lengthₜ t = 0
-- The Length of a Term:1 ends here

-- [[The Length of a Term][The Length of a Term:2]]
_ : lengthₜ (quoteTerm (Σ x ∶ ℕ • x ≡ x)) ≡ 10
_ = refl
-- The Length of a Term:2 ends here

-- [[Decreasing de Brujin Indices][Decreasing de Brujin Indices:1]]
var-dec₀ : (fuel : ℕ) → Term → Term
var-dec₀ zero t  = t
-- Let's use an “impossible” term.
var-dec₀ (suc n) (var zero args)      = def (quote ⊥) []
var-dec₀ (suc n) (var (suc x) args)   = var x args
var-dec₀ (suc n) (con c args)         = con c (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (def f args)         = def f (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (lam v (abs s x))    = lam v (abs s (var-dec₀ n x))
var-dec₀ (suc n) (pat-lam cs args)    = pat-lam cs (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (Π[ s ∶ arg i A ] B) = Π[ s ∶ arg i (var-dec₀ n A) ] var-dec₀ n B
{-# CATCHALL #-}
-- sort, lit, meta, unknown
var-dec₀ n t = t
-- Decreasing de Brujin Indices:1 ends here

-- [[Decreasing de Brujin Indices][Decreasing de Brujin Indices:2]]
var-dec : Term → Term
var-dec t = var-dec₀ (lengthₜ t) t
-- Decreasing de Brujin Indices:2 ends here

-- [[Decreasing de Brujin Indices][Decreasing de Brujin Indices:3]]
_ : ∀ {x : ℕ} → var-dec (quoteTerm x) ≡ quoteTerm ⊥
_ = refl
-- Decreasing de Brujin Indices:3 ends here

-- [[Context Monad][Context Monad:1]]
Context = λ ℓ → ℕ → Set ℓ

infix -1000 ‵_
‵_ : ∀ {ℓ} → Set ℓ → Context ℓ
‵ S = λ _ → S

End : ∀ {ℓ} → Context ℓ
End = ‵ ⊤

End₀ = End {ℓ₀}

_>>=_ : ∀ {a b}
      → (Γ : Set a)  -- Main diference
      → (Γ → Context b)
      → Context (a ⊍ b)
(Γ >>= f) ℕ.zero  = Σ γ ∶ Γ • f γ 0
(Γ >>= f) (suc n) = (γ : Γ) → f γ n
-- Context Monad:1 ends here

-- [[⟨⟩ Notation][⟨⟩ Notation:1]]
-- Expressions of the form “⋯ , tt” may now be written “⟨ ⋯ ⟩”
infixr 5 ⟨ _⟩
⟨⟩ : ∀ {ℓ} → ⊤ {ℓ}
⟨⟩ = tt

⟨ : ∀ {ℓ} {S : Set ℓ} → S → S
⟨ s = s

_⟩ : ∀ {ℓ} {S : Set ℓ} → S → S × ⊤ {ℓ}
s ⟩ = s , tt
-- ⟨⟩ Notation:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::sec:pi-to-lambda][Π→λ:1]]
Π→λ-helper : Term → Term
Π→λ-helper (pi  a b)         = lam visible b
Π→λ-helper (lam a (abs x y)) = lam a (abs x (Π→λ-helper y))
{-# CATCHALL #-}
Π→λ-helper x = x

macro
  Π→λ : Term → Term → TC Unit.⊤
  Π→λ tm goal = normalise tm >>=ₘ λ tm′ → unify (Π→λ-helper tm′) goal
-- Π→λ:1 ends here

-- [[~_:waist_~][~_:waist_~:1]]
waist-helper : ℕ → Term → Term
waist-helper zero t    = t
waist-helper (suc n) t = waist-helper n (Π→λ-helper t)

macro
  _:waist_ : Term → Term → Term → TC Unit.⊤
  _:waist_ t 𝓃 goal =      normalise (t app 𝓃)
                      >>=ₘ λ t′ → unify (waist-helper (toℕ 𝓃) t′) goal
-- ~_:waist_~:1 ends here

-- [[Field projections][Field projections:1]]
Field₀ : ℕ → Term → Term
Field₀ zero c    = def (quote proj₁) (arg (arg-info visible relevant) c ∷ [])
Field₀ (suc n) c = Field₀ n (def (quote proj₂) (arg (arg-info visible relevant) c ∷ []))

macro
  Field : ℕ → Term → Term → TC Unit.⊤
  Field n t goal = unify goal (Field₀ n t)
-- Field projections:1 ends here

-- [[Stage 3: Sources][Stage 3: Sources:1]]
_ :   quoteTerm (∀ {x : ℕ} → ℕ)
    ≡ pi (arg (arg-info hidden relevant) (quoteTerm ℕ)) (abs "x" (quoteTerm ℕ))
_ = refl
-- Stage 3: Sources:1 ends here

-- [[Stage 3: Sources][Stage 3: Sources:2]]
sources₀ : Term → Term
-- Otherwise:
sources₀ (Π[ a ∶ arg i A ] (Π[ b ∶ arg _ Ba ] Cab)) =
    def (quote _×_) (vArg A
                    ∷ vArg (def (quote _×_)
                                (vArg (var-dec Ba)
                                     ∷ vArg (var-dec (var-dec (sources₀ Cab))) ∷ []))
                    ∷ [])
sources₀ (Π[ a ∶ arg (arg-info hidden _) A ] Ba) = quoteTerm 𝟘
sources₀ (Π[ x ∶ arg i A ] Bx) = A
{-# CATCHALL #-}
-- sort, lit, meta, unknown
sources₀ t = quoteTerm 𝟙

{-# TERMINATING #-}
sources₁ : Term → Term
sources₁ (Π[ a ∶ arg (arg-info hidden _) A ] Ba) = quoteTerm 𝟘
sources₁ (Π[ a ∶ arg i A ] (Π[ b ∶ arg _ Ba ] Cab)) = def (quote _×_) (vArg A ∷
  vArg (def (quote _×_) (vArg (var-dec Ba)
                             ∷ vArg (var-dec (var-dec (sources₀ Cab))) ∷ [])) ∷ [])
sources₁ (Π[ x ∶ arg i A ] Bx) = A
sources₁ (def (quote Σ) (ℓ₁ ∷ ℓ₂ ∷ τ ∷ body))
    = def (quote Σ) (ℓ₁ ∷ ℓ₂ ∷ map-Arg sources₀ τ ∷ List.map (map-Arg sources₁) body)
-- This function introduces 𝟙s, so let's drop any old occurances a la 𝟘.
sources₁ (def (quote ⊤) _) = def (quote 𝟘) []
sources₁ (lam v (abs s x))     = lam v (abs s (sources₁ x))
sources₁ (var x args) = var x (List.map (map-Arg sources₁) args)
sources₁ (con c args) = con c (List.map (map-Arg sources₁) args)
sources₁ (def f args) = def f (List.map (map-Arg sources₁) args)
sources₁ (pat-lam cs args) = pat-lam cs (List.map (map-Arg sources₁) args)
{-# CATCHALL #-}
-- sort, lit, meta, unknown
sources₁ t = t
-- Stage 3: Sources:2 ends here

-- [[Stage 3: Sources][Stage 3: Sources:3]]
macro
  sources : Term → Term → TC Unit.⊤
  sources tm goal = normalise tm >>=ₘ λ tm′ → unify (sources₁ tm′) goal

_ : sources (ℕ → Set) ≡ ℕ
_ = refl

_ : sources (Σ x ∶ (ℕ → Fin 3) • ℕ) ≡ (Σ x ∶ ℕ • ℕ)
_ = refl

_ : ∀ {ℓ : Level} {A B C : Set}
  → sources (Σ x ∶ (A → B) • C) ≡ (Σ x ∶ A • C)
_ = refl

_ : sources (Fin 1 → Fin 2 → Fin 3) ≡ (Σ _ ∶ Fin 1 • Fin 2 × 𝟙)
_ = refl

_ : sources (Σ f ∶ (Fin 1 → Fin 2 → Fin 3 → Fin 4) • Fin 5)
  ≡ (Σ f ∶ (Fin 1 × Fin 2 × Fin 3) • Fin 5)
_ = refl

_ : ∀ {A B C : Set} → sources (A → B → C) ≡ (A × B × 𝟙)
_ = refl

_ : ∀ {A B C D E : Set} → sources (A → B → C → D → E)
                        ≡ Σ A (λ _ → Σ B (λ _ → Σ C (λ _ → Σ D (λ _ → ⊤))))
_ = refl
-- Stage 3: Sources:3 ends here

-- [[Stage 3: Sources][Stage 3: Sources:4]]
-- one implicit
_ : sources (∀ {x : ℕ} → x ≡ x) ≡ 𝟘
_ = refl

-- multiple implicits
_ : sources (∀ {x y z : ℕ} → x ≡ y) ≡ 𝟘
_ = refl
-- Stage 3: Sources:4 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::sec:sigma-to-sum][Stage 4: ~Σ→⊎~ --Replacing Products with Sums:1]]
{-# TERMINATING #-}
Σ→⊎₀ : Term → Term
Σ→⊎₀ (def (quote Σ) (𝒽₁ ∷ 𝒽₀ ∷ arg i A ∷ arg i₁ (lam v (abs s x)) ∷ []))
  =  def (quote _⊎_) (𝒽₁ ∷ 𝒽₀ ∷ arg i A ∷ vArg (Σ→⊎₀ (var-dec x)) ∷ [])
-- Interpret “End” in do-notation to be an empty, impossible, constructor.
Σ→⊎₀ (def (quote ⊤) _) = def (quote ⊥) []
 -- Walk under λ's and Π's.
Σ→⊎₀ (lam v (abs s x)) = lam v (abs s (Σ→⊎₀ x))
Σ→⊎₀ (Π[ x ∶ A ] Bx) = Π[ x ∶ A ] Σ→⊎₀ Bx
{-# CATCHALL #-}
Σ→⊎₀ t = t

macro
  Σ→⊎ : Term → Term → TC Unit.⊤
  Σ→⊎ tm goal = normalise tm >>=ₘ λ tm′ → unify (Σ→⊎₀ tm′) goal
-- Stage 4: ~Σ→⊎~ --Replacing Products with Sums:1 ends here

-- [[Stage 4: ~Σ→⊎~ --Replacing Products with Sums][Stage 4: ~Σ→⊎~ --Replacing Products with Sums:2]]
_ : Σ→⊎ (Π X ∶ Set • (X → X))     ≡ (Π X ∶ Set • (X → X)); _ = refl
_ : Σ→⊎ (Π X ∶ Set • Σ s ∶ X • X) ≡ (Π X ∶ Set • X ⊎ X)  ; _ = refl
_ : Σ→⊎ (Π X ∶ Set • Σ s ∶ (X → X) • X) ≡ (Π X ∶ Set • (X → X) ⊎ X)  ; _ = refl
_ : Σ→⊎ (Π X ∶ Set • Σ z ∶ X • Σ s ∶ (X → X) • ⊤ {ℓ₀}) ≡ (Π X ∶ Set • X ⊎ (X → X) ⊎ ⊥)
_ = refl
-- Stage 4: ~Σ→⊎~ --Replacing Products with Sums:2 ends here

-- [[Stage 5: Fixpoint and proof that ~𝔻 ≅ ℕ~][Stage 5: Fixpoint and proof that ~𝔻 ≅ ℕ~:1]]
{-# NO_POSITIVITY_CHECK #-}
data Fix {ℓ} (F : Set ℓ → Set ℓ) : Set ℓ where
  μ : F (Fix F) → Fix F
-- Stage 5: Fixpoint and proof that ~𝔻 ≅ ℕ~:1 ends here

-- [[~termtype~ and ~Inj~ macros][~termtype~ and ~Inj~ macros:1]]
macro
  termtype : Term → Term → TC Unit.⊤
  termtype tm goal =
                normalise tm
           >>=ₘ λ tm′ → unify goal (def (quote Fix) ((vArg (Σ→⊎₀ (sources₁ tm′))) ∷ []))
-- ~termtype~ and ~Inj~ macros:1 ends here

-- [[~termtype~ and ~Inj~ macros][~termtype~ and ~Inj~ macros:2]]
Inj₀ : ℕ → Term → Term
Inj₀ zero c    = con (quote inj₁) (arg (arg-info visible relevant) c ∷ [])
Inj₀ (suc n) c = con (quote inj₂) (vArg (Inj₀ n c) ∷ [])

-- Duality!
-- 𝒾-th projection: proj₁ ∘ (proj₂ ∘ ⋯ ∘ proj₂)
-- 𝒾-th injection:  (inj₂ ∘ ⋯ ∘ inj₂) ∘ inj₁

macro
  Inj : ℕ → Term → Term → TC Unit.⊤
  Inj n t goal = unify goal ((con (quote μ) []) app (Inj₀ n t))
-- ~termtype~ and ~Inj~ macros:2 ends here

-- [[The ~_:kind_~ meta-primitive][The ~_:kind_~ meta-primitive:1]]
data Kind : Set where
  ‵record    : Kind
  ‵typeclass : Kind
  ‵data      : Kind

macro
  _:kind_ : Term → Term → Term → TC Unit.⊤
  _:kind_ t (con (quote ‵record) _)    goal = normalise (t app (quoteTerm 0))
                      >>=ₘ λ t′ → unify (waist-helper 0 t′) goal
  _:kind_ t (con (quote ‵typeclass) _) goal = normalise (t app (quoteTerm 1))
                      >>=ₘ λ t′ → unify (waist-helper 1 t′) goal
  _:kind_ t (con (quote ‵data) _) goal = normalise (t app (quoteTerm 1))
                      >>=ₘ λ t′ → normalise (waist-helper 1 t′)
                      >>=ₘ λ t″ → unify goal (def (quote Fix)
                                                  ((vArg (Σ→⊎₀ (sources₁ t″))) ∷ []))
  _:kind_ t _ goal = unify t goal
-- The ~_:kind_~ meta-primitive:1 ends here
