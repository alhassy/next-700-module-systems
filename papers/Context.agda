-- [[file:~/thesis-proposal/papers/Paper2.org::*APPENDICES][APPENDICES:1]]
module Context where
-- APPENDICES:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Imports][Imports:1]]
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

-- [[file:~/thesis-proposal/papers/Paper2.org::*Quantifiers Π∶•/Σ∶• and Products/Sums][Quantifiers Π∶•/Σ∶• and Products/Sums:1]]
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

-- [[file:~/thesis-proposal/papers/Paper2.org::*⟨⟩ Notation][⟨⟩ Notation:1]]
-- Expressions of the form “⋯ , tt” may now be written “⟨ ⋯ ⟩”
infixr 5 ⟨ _⟩
⟨⟩ : ∀ {ℓ} → ⊤ {ℓ}
⟨⟩ = tt

⟨ : ∀ {ℓ} {S : Set ℓ} → S → S
⟨ s = s

_⟩ : ∀ {ℓ} {S : Set ℓ} → S → S × ⊤ {ℓ}
s ⟩ = s , tt
-- ⟨⟩ Notation:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Reflection][Reflection:1]]
import Data.Unit as Unit
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₘ_)

-- Single argument application
_app_ : Term → Term → Term
(def f args) app arg′ = def f (args ∷ʳ arg (arg-info visible relevant) arg′)
(con f args) app arg′ = con f (args ∷ʳ arg (arg-info visible relevant) arg′)
{-# CATCHALL #-}
tm app arg′ = tm

-- Reify ℕ term encodings as ℕ values
toℕ : Term → ℕ
toℕ (lit (nat n)) = n
{-# CATCHALL #-}
toℕ _ = 0

arg-term : ∀ {ℓ} {A : Set ℓ} → (Term → A) → Arg Term → A
arg-term f (arg i x) = f x

{-# TERMINATING #-}
var-dec₀ : (fuel : ℕ) → Term → Term
var-dec₀ zero t  = t
-- var-dec₀ (suc n) (var Fin.0F args) = var Fin.0F args
-- Let's use an “impossible” term.
var-dec₀ (suc n) (var zero args)    = def (quote ⊥) []
var-dec₀ (suc n) (var (suc x) args)   = var x args
var-dec₀ (suc n) (con c args)         = con c (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (def f args)         = def f (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (lam v (abs s x))    = lam v (abs s (var-dec₀ n x))
var-dec₀ (suc n) (pat-lam cs args)    = pat-lam cs (map-Args (var-dec₀ n) args)
var-dec₀ (suc n) (Π[ s ∶ arg i A ] B) = Π[ s ∶ arg i (var-dec₀ n A) ] var-dec₀ n B
{-# CATCHALL #-}
-- sort, lit, meta, unknown
var-dec₀ n t = t

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

_ : lengthₜ (quoteTerm (Σ x ∶ ℕ • x ≡ x)) ≡ 10
_ = refl

var-dec : Term → Term
var-dec t = var-dec₀ (lengthₜ t) t

_ :   var-dec (quoteTerm ((X : Set) → X))
    ≡ pi (vArg (sort (lit 0))) (abs "X" (def (quote ⊥) []))
_ = refl
-- Reflection:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Context Monad][Context Monad:1]]
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

-- [[file:~/thesis-proposal/papers/Paper2.org::*Monoid Context][Monoid Context:1]]
Monoid : ∀ ℓ → Context (ℓsuc ℓ)
Monoid ℓ = do Carrier ← Set ℓ
              Id      ← Carrier
              _⊕_     ← (Carrier → Carrier → Carrier)
              leftId  ← ∀ {x : Carrier} → x ⊕ Id ≡ x
              rightId ← ∀ {x : Carrier} → Id ⊕ x ≡ x
              assoc   ← ∀ {x y z} → (x ⊕ y) ⊕ z  ≡  x ⊕ (y ⊕ z)
              End {ℓ}
-- Monoid Context:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*DynamicSystem Context][DynamicSystem Context:1]]
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

idτ : Set₁
idτ = ∀ (X : Set) (e : X) → X

id₁ : ∀ (X : Set) → Set
id₁ = λ (X : Set) → ((e : X) → X)

id₂ : ∀ (X : Set) (e : X) → Set
id₂ = λ (X : Set) (e : X) → X
-- DynamicSystem Context:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Π→λ and :waist][Π→λ and :waist:1]]
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

_ : DynamicSystem 0 ≡ DynamicSystem :waist 0
_ = refl

-- _ : ∀ {ℓ} {Γ : Context (ℓsuc ℓ)} → Γ 0 ≡ {! Γ :waist 0 !}
-- _ = refl

𝒩⁰ : A′
𝒩⁰ = ⟨ ℕ , 0 , suc ⟩

𝒩¹ : B′ ℕ
𝒩¹ = ⟨ 0 , suc ⟩

𝒩² : C′ ℕ 0
𝒩² = ⟨ suc ⟩

𝒩³ : D′ ℕ 0 suc
𝒩³ = ⟨⟩
-- Π→λ and :waist:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Field projections][Field projections:1]]
Field₀ : ℕ → Term → Term
Field₀ zero c    = def (quote proj₁) (arg (arg-info visible relevant) c ∷ [])
Field₀ (suc n) c = Field₀ n (def (quote proj₂) (arg (arg-info visible relevant) c ∷ []))

macro
  Field : ℕ → Term → Term → TC Unit.⊤
  Field n t goal = unify goal (Field₀ n t)
-- Field projections:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Termtypes][Termtypes:1]]
{-# NO_POSITIVITY_CHECK #-}
data Fix {ℓ} (F : Set ℓ → Set ℓ) : Set ℓ where
  μ : F (Fix F) → Fix F

D₁ = DynamicSystem 0

1-records : D₁ ≡ (Σ X ∶ Set • Σ z ∶ X • Σ s ∶ (X → X) • ⊤)
1-records = refl

D₂ = DynamicSystem :waist 1

2-funcs : D₂ ≡ (λ (X : Set) → Σ z ∶ X • Σ s ∶ (X → X) • ⊤)
2-funcs = refl

-- useful to motivate defn of sources₀
_ :   quoteTerm (∀ {x : ℕ} → ℕ)
    ≡ pi (arg (arg-info hidden relevant) (quoteTerm ℕ)) (abs "x" (quoteTerm ℕ))
_ = refl

sources₀ : Term → Term
-- Otherwise:
sources₀ (Π[ a ∶ arg i A ] (Π[ b ∶ arg _ Ba ] Cab)) = def (quote _×_) (vArg A ∷
  vArg (def (quote _×_) (vArg (var-dec Ba) ∷ vArg (var-dec (var-dec (sources₀ Cab))) ∷ [])) ∷ [])
  -- sources₀ (Π[ a ∶ arg i A ] (Π[ b ∶ Ba ] Cab)) = Π[ a ∶ arg i A ] Π[ b ∶ Ba ] sources₀ Cab
-- Design descision: Types starting with implicit arguments are ‘invariants’, not ‘constructors’ ⇐ Couldn't do this.
sources₀ (Π[ a ∶ arg (arg-info hidden _) A ] Ba) = quoteTerm 𝟘
-- Another attempt: If it has a “≡” then an invariant.
-- sources₀ (Π[ a ∶ arg i A ] (def (quote _≡_) args)) = quoteTerm 𝟘
sources₀ (Π[ x ∶ arg i A ] Bx) = A
{-# CATCHALL #-}
-- sort, lit, meta, unknown
sources₀ t = quoteTerm 𝟙

{-# TERMINATING #-}
sources₁ : Term → Term
sources₁ (Π[ a ∶ arg (arg-info hidden _) A ] Ba) = quoteTerm 𝟘
sources₁ (Π[ a ∶ arg i A ] (Π[ b ∶ arg _ Ba ] Cab)) = def (quote _×_) (vArg A ∷
  vArg (def (quote _×_) (vArg (var-dec Ba) ∷ vArg (var-dec (var-dec (sources₀ Cab))) ∷ [])) ∷ [])
-- sources₁ (Π[ a ∶ arg i A ] (Π[ b ∶ arg _ Ba ] Cab)) = def (quote _×_) (vArg A ∷ vArg Ba ∷ [])
sources₁ (Π[ x ∶ arg i A ] Bx) = A
sources₁ (def (quote Σ) (ℓ₁ ∷ ℓ₂ ∷ τ ∷ body)) = def (quote Σ) (ℓ₁ ∷ ℓ₂ ∷ map-Arg sources₀ τ ∷ List.map (map-Arg sources₁) body)
sources₁ (def (quote ⊤) _) = def (quote 𝟘) [] -- This function introduces 𝟙s, so let's drop any old occurances a la 𝟘.
sources₁ (lam v (abs s x))     = lam v (abs s (sources₁ x))
sources₁ (var x args) = var x (List.map (map-Arg sources₁) args)
sources₁ (con c args) = con c (List.map (map-Arg sources₁) args)
sources₁ (def f args) = def f (List.map (map-Arg sources₁) args)
sources₁ (pat-lam cs args) = pat-lam cs (List.map (map-Arg sources₁) args)
{-# CATCHALL #-}
-- sort, lit, meta, unknown
sources₁ t = t

macro
  sources : Term → Term → TC Unit.⊤
  sources tm goal = normalise tm >>=ₘ λ tm′ → unify (sources₁ tm′) goal

_ : sources (ℕ → Set) ≡ ℕ ; _ = refl
-- _ : sources (λ (x : (ℕ → Fin 3)) → ℕ) ≡ λ (x : ℕ) → ℕ ; _ = refl
_ : sources (Σ x ∶ (ℕ → Fin 3) • ℕ) ≡ (Σ x ∶ ℕ • ℕ) ; _ = refl
_ : ∀ {ℓ : Level} {A B C : Set} → sources (Σ x ∶ (A → B) • C) ≡ (Σ x ∶ A • C) ; _ = refl
-- MA: Heterogenous levels wont work; e.g., A ≔ ℕ crashes.
_ : sources (Fin 1 → Fin 2 → Fin 3) ≡ (Σ _ ∶ Fin 1 • Fin 2 × 𝟙) ; _ = refl
_ : sources (Σ f ∶ (Fin 1 → Fin 2 → Fin 3 → Fin 4) • Fin 5) ≡ (Σ f ∶ (Fin 1 × Fin 2 × Fin 3) • Fin 5) ; _ = refl
_ : ∀ {A B C : Set} → sources (A → B → C) ≡ (A × B × 𝟙) ; _ = refl
_ : ∀ {A B C D E : Set} → sources (A → B → C → D → E) ≡ Σ A (λ _ → Σ B (λ _ → Σ C (λ _ → Σ D (λ _ → ⊤)))) ; _ = refl
-- Not desirable:
-- _ : sources (∀ {x : ℕ} → x ≡ x) ≡ ℕ ; _ = refl
-- Design descision: Types starting with implicit arguments are ‘invariants’, not ‘constructors’
_ : sources (∀ {x : ℕ} → x ≡ x) ≡ 𝟘 ; _ = refl -- one implicit
_ : sources (∀ {x y z : ℕ} → x ≡ y) ≡ 𝟘 ; _ = refl   -- multiple implicits

D₃ = sources D₂

3-sources : D₃ ≡ λ (X : Set) → Σ z ∶ 𝟙 • Σ s ∶ X • 𝟘
3-sources = refl

{-# TERMINATING #-}
Σ→⊎₀ : Term → Term
Σ→⊎₀ (def (quote Σ) (𝒽₁ ∷ 𝒽₀ ∷ arg i A ∷ arg i₁ (lam v (abs s x)) ∷ []))
  =  def (quote _⊎_) (𝒽₁ ∷ 𝒽₀ ∷ arg i A ∷ vArg (Σ→⊎₀ (var-dec x)) ∷ [])
  -- def (quote _⊎_) (𝒽₁ ∷ 𝒽₀ ∷ arg i (var-dec A) ∷ vArg (Σ→⊎₀ (var-dec x)) ∷ [])
Σ→⊎₀ (def (quote ⊤) _) = def (quote ⊥) [] -- Interpret “End” in do-notation to be an empty, impossible, constructor.
 -- Walk under λ's and Π's.
Σ→⊎₀ (lam v (abs s x)) = lam v (abs s (Σ→⊎₀ x))
Σ→⊎₀ (Π[ x ∶ A ] Bx) = Π[ x ∶ A ] Σ→⊎₀ Bx
{-# CATCHALL #-}
Σ→⊎₀ t = t

macro
  Σ→⊎ : Term → Term → TC Unit.⊤
  Σ→⊎ tm goal = normalise tm >>=ₘ λ tm′ → unify (Σ→⊎₀ tm′) goal

-- _ :   Σ→⊎ (Σ x ∶ ℕ • ⊤ {ℓ₀})
--     ≡ (ℕ ⊎ ⊥)
-- _ = refl

-- Fails due to the ⊥-choice above.
-- _ :   ∀ {C : Set} → Σ→⊎ (Σ x ∶ C • Σ y ∶ C • ⊤ {ℓ₀})
--                   ≡ (C ⊎ C ⊎ ⊤)
-- _ = refl

-- Unit tests
_ : Σ→⊎ (Π X ∶ Set • (X → X))     ≡ (Π X ∶ Set • (X → X)); _ = refl
_ : Σ→⊎ (Π X ∶ Set • Σ s ∶ X • X) ≡ (Π X ∶ Set • X ⊎ X)  ; _ = refl
_ : Σ→⊎ (Π X ∶ Set • Σ s ∶ (X → X) • X) ≡ (Π X ∶ Set • (X → X) ⊎ X)  ; _ = refl
_ : Σ→⊎ (Π X ∶ Set • Σ z ∶ X • Σ s ∶ (X → X) • ⊤ {ℓ₀}) ≡ (Π X ∶ Set • X ⊎ (X → X) ⊎ ⊥)  ; _ = refl

D₄ = Σ→⊎ D₃

4-unions : D₄ ≡ λ X → 𝟙 ⊎ X ⊎ 𝟘
4-unions = refl

𝔻 = Fix D₄

-- Pattern synonyms for more compact presentation
pattern zeroD  = μ (inj₁ tt)       -- : 𝔻
pattern sucD e = μ (inj₂ (inj₁ e)) -- : 𝔻 → 𝔻

oh : 𝔻 → ℕ
oh zeroD    = 0
oh (sucD x) = suc (oh x)

ho : ℕ → 𝔻
ho zero    = zeroD
ho (suc n) = sucD (ho n)

oh∘ho : ∀ n → oh (ho n) ≡ n
oh∘ho zero    = refl
oh∘ho (suc n) = cong suc (oh∘ho n)

ho∘oh : ∀ d → ho (oh d) ≡ d
ho∘oh zeroD    = refl
ho∘oh (sucD x) = cong sucD (ho∘oh x)
-- Termtypes:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*~termtype~][~termtype~:1]]
Inj₀ : ℕ → Term → Term
Inj₀ zero c    = con (quote inj₁) (arg (arg-info visible relevant) c ∷ [])
Inj₀ (suc n) c = con (quote inj₂) (vArg (Inj₀ n c) ∷ [])

-- Duality!
-- 𝒾-th projection: proj₁ ∘ (proj₂ ∘ ⋯ ∘ proj₂)
-- 𝒾-th injection:  (inj₂ ∘ ⋯ ∘ inj₂) ∘ inj₁

macro
  Inj : ℕ → Term → Term → TC Unit.⊤
  Inj n t goal = unify goal ((con (quote μ) []) app (Inj₀ n t))

baseD : 𝔻
baseD = Inj 0 (tt {ℓ₀})

nextD′ : 𝔻 → 𝔻
nextD′ d = Inj 1 d

_ : zeroD ≡ baseD
_ = refl

macro
  termtype : Term → Term → TC Unit.⊤
  termtype tm goal =
                normalise tm
           >>=ₘ λ tm′ → unify goal (def (quote Fix) ((vArg (Σ→⊎₀ (sources₁ tm′))) ∷ []))
-- ~termtype~:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Monoid termtype][Monoid termtype:1]]
𝕄 : Set
𝕄 = termtype (Monoid ℓ₀ :waist 1)
{- ie Fix (λ X → 𝟙         -- Id, nil leaf
               ⊎ X × X × 𝟙 -- _⊕_, branch
               ⊎ 𝟘         -- src of leftId
               ⊎ 𝟘         -- src of rightId
               ⊎ X × X × 𝟘 -- src of assoc
               ⊎ 𝟘)        -- the “End {ℓ}”
-}

-- Pattern synonyms for more compact presentation
pattern emptyM      = μ (inj₁ tt)                      -- : 𝕄
pattern branchM l r = μ (inj₂ (inj₁ (l , r , tt)))     -- : 𝕄 → 𝕄 → 𝕄
pattern absurdM a   = μ (inj₂ (inj₂ (inj₂ (inj₂ a))))  -- absurd values of 𝟘

data TreeSkeleton : Set where
  empty  : TreeSkeleton
  branch : TreeSkeleton → TreeSkeleton → TreeSkeleton

𝕄→Tree : 𝕄 → TreeSkeleton
𝕄→Tree emptyM = empty
𝕄→Tree (branchM l r) = branch (𝕄→Tree l) (𝕄→Tree r)
𝕄→Tree (absurdM (inj₁ ()))
𝕄→Tree (absurdM (inj₂ ()))

𝕄←Tree : TreeSkeleton → 𝕄
𝕄←Tree empty = emptyM
𝕄←Tree (branch l r) = branchM (𝕄←Tree l) (𝕄←Tree r)

𝕄←Tree∘𝕄→Tree : ∀ m → 𝕄←Tree (𝕄→Tree m) ≡ m
𝕄←Tree∘𝕄→Tree emptyM = refl
𝕄←Tree∘𝕄→Tree (branchM l r) = cong₂ branchM (𝕄←Tree∘𝕄→Tree l) (𝕄←Tree∘𝕄→Tree r)
𝕄←Tree∘𝕄→Tree (absurdM (inj₁ ()))
𝕄←Tree∘𝕄→Tree (absurdM (inj₂ ()))

𝕄→Tree∘𝕄←Tree : ∀ t → 𝕄→Tree (𝕄←Tree t) ≡ t
𝕄→Tree∘𝕄←Tree empty = refl
𝕄→Tree∘𝕄←Tree (branch l r) = cong₂ branch (𝕄→Tree∘𝕄←Tree l) (𝕄→Tree∘𝕄←Tree r)

-- “a pointed set that contains Ξ” ─c.f., “a group over Ξ”
-- Monoid termtype:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*~:kind~][~:kind~:1]]
data Kind : Set where
  ‵record    : Kind
  ‵typeclass : Kind
  ‵data      : Kind

{- Nope: Since :waist may return type constructors, not sets!
_:kind_ : ∀ {ℓ} → Context ℓ → Kind → Set ℓ
𝒞 :kind ‵record    = 𝒞 :waist 0
𝒞 :kind ‵typeclass = 𝒞 :waist 1
𝒞 :kind ‵data      = termtype (𝒞 :waist 1)
-}
macro
  _:kind_ : Term → Term → Term → TC Unit.⊤
  _:kind_ t (con (quote ‵record) _)    goal = normalise (t app (quoteTerm 0))
                      >>=ₘ λ t′ → unify (waist-helper 0 t′) goal
  _:kind_ t (con (quote ‵typeclass) _) goal = normalise (t app (quoteTerm 1))
                      >>=ₘ λ t′ → unify (waist-helper 1 t′) goal
  _:kind_ t (con (quote ‵data) _) goal = normalise (t app (quoteTerm 1))
                      >>=ₘ λ t′ → normalise (waist-helper 1 t′)
                      >>=ₘ λ t″ → unify goal (def (quote Fix) ((vArg (Σ→⊎₀ (sources₁ t″))) ∷ []))
  _:kind_ t _ goal = unify t goal

-- _⟴_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- x ⟴ f = f x
-- ~:kind~:1 ends here


--------------------------------------------------------------------------------

VecSpcSig : Context ℓ₁
VecSpcSig = do F   ← Set
               V   ← Set
               𝟘   ← F
               𝟙   ← F
               _+_ ← (F → F → F)
               o   ← V
               _*_ ← (F → V → V)
               _·_ ← (V → V → F)
               End₀

VSInterface : (Field Vectors : Set) → Set
VSInterface F V = (VecSpcSig :waist 2) F V

VSTerm : (Field : Set) → Set
VSTerm = λ F → termtype ((VecSpcSig :waist 2) F)
{- ≅  Fix (λ X → 𝟙     -- Representation of additive unit, zero
               ⊎ 𝟙     -- Representation of multiplicative unit, one
               ⊎ F × F -- Pair of scalars to be summed
               ⊎ 𝟙     -- Representation of the zero vector
               ⊎ F × X -- Pair of arguments to be scalar-producted
               ⊎ X × X -- Pair of vectors to be dot-producted
-}

pattern 𝟘ₛ = μ (inj₁ tt)
pattern 𝟙ₛ = μ (inj₂ (inj₁ tt))
pattern _+ₛ_ x y = μ (inj₂ (inj₂ (inj₁ (x , (y , tt)))))
pattern 𝟘ᵥ = μ (inj₂ (inj₂ (inj₂ (inj₁ tt))))
pattern _*ᵥ_ x xs = μ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (x , (xs , tt)))))))
pattern _·ᵥ_ xs ys = μ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (xs , (ys , tt))))))))

data ℝ𝕚𝕟𝕘 (Scalar : Set) : Set where
  zeroₛ : ℝ𝕚𝕟𝕘 Scalar
  oneₛ  : ℝ𝕚𝕟𝕘 Scalar
  plusₛ : Scalar → Scalar → ℝ𝕚𝕟𝕘 Scalar
  zeroᵥ : ℝ𝕚𝕟𝕘 Scalar
  prod  : Scalar → ℝ𝕚𝕟𝕘 Scalar → ℝ𝕚𝕟𝕘 Scalar
  dot   : ℝ𝕚𝕟𝕘 Scalar → ℝ𝕚𝕟𝕘 Scalar → ℝ𝕚𝕟𝕘 Scalar

view : ∀ {F} → VSTerm F → ℝ𝕚𝕟𝕘 F
view 𝟘ₛ = zeroₛ
view 𝟙ₛ = oneₛ
view (x +ₛ y) = plusₛ x y
view 𝟘ᵥ = zeroᵥ
view (x *ᵥ xs) = prod x (view xs)
view (xs ·ᵥ ys) = dot (view xs) (view ys)

--------------------------------------------------------------------------------

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

to : ∀ {E} → ℂ E → List E
to (e :: es) = e ∷ to es
to ∅ = []
