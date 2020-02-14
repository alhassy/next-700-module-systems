module semantics-with-waist where

open import Level renaming (_⊔_ to _⊍_; suc to ℓsuc; zero to ℓ₀)
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Bool using (Bool ; true ; false)
open import Data.List as List using (List ; [] ; _∷_ ; _∷ʳ_; sum)
open import Function using (_∘_)
open import Data.Sum
open import Data.Fin  as Fin using (Fin)
open import Data.Maybe  hiding (_>>=_)

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

open import Data.Product

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

open import Data.Empty using (⊥)

𝟙 = ⊤ {ℓ₀}
𝟘 = ⊥

-- Expressions of the form “⋯ , tt” may now be written “⟨ ⋯ ⟩”
infixr 5 ⟨ _⟩
⟨⟩ : ∀ {ℓ} → ⊤ {ℓ}
⟨⟩ = tt

⟨ : ∀ {ℓ} {S : Set ℓ} → S → S
⟨ s = s

_⟩ : ∀ {ℓ} {S : Set ℓ} → S → S × ⊤ {ℓ}
s ⟩ = s , tt

import Data.Unit as Unit
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₘ_)

-- Single argument application
_app_ : Term → Term → Term
(def f args) app arg′ = def f (args ∷ʳ arg (arg-info visible relevant) arg′) -- keep existing arguments!
{-# CATCHALL #-}
tm app arg′ = tm

-- Reify ℕ term encodings as ℕ values
toℕ : Term → ℕ
toℕ (lit (nat n)) = n
{-# CATCHALL #-}
toℕ _ = 0

arg-term : ∀ {ℓ} {A : Set ℓ} → (Term → A) → Arg Term → A
arg-term f (arg i x) = f x

var-dec₀ : (fuel : ℕ) → Term → Term
var-dec₀ Fin.0F t  = t
-- var-dec₀ (suc n) (var Fin.0F args) = var Fin.0F args
-- Let's use an “impossible” term.
var-dec₀ (suc n) (var Fin.0F args)    = def (quote ⊥) []
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

Collection : ∀ ℓ → Context (ℓsuc ℓ)
Collection ℓ = do
  Elem    ← Set ℓ
  Carrier ← Set ℓ
  insert  ← (Elem → Carrier → Carrier)
  ∅       ← Carrier
  isEmpty ← (Carrier → Bool)
  insert-nonEmpty ← ∀ {e : Elem} {x : Carrier} → isEmpty (insert e x) ≡ false
  End {ℓ}

ListColl : {ℓ : Level} → Collection ℓ 1
ListColl E = ⟨ List E
             , _∷_
             , []
             , (λ { [] → true; _ → false})
             , (λ {x} {x = x₁} → refl)
             ⟩

ℕCollection = (Collection ℓ₀ :waist 2)
                ("Elem"    ≔ Digit)
                ("Carrier" ≔ ℕ)
--
-- i.e., (Collection ℓ₀ :waist 2) Digit ℕ

stack : ℕCollection
stack = ⟨ "insert"      ≔ (λ d s → suc (10 * s + #→ℕ d))
        , "empty stack" ≔ 0
        , "is-empty"    ≔ (λ { 0 → true; _ → false})
        -- Properties --
        , (λ {d : Digit} {s : ℕ} → refl {x = false})
        ⟩

Field₀ : ℕ → Term → Term
Field₀ zero c    = def (quote proj₁) (arg (arg-info visible relevant) c ∷ [])
Field₀ (suc n) c = Field₀ n (def (quote proj₂) (arg (arg-info visible relevant) c ∷ []))

macro
  Field : ℕ → Term → Term → TC Unit.⊤
  Field n t goal = unify goal (Field₀ n t)

Elem      : ∀ {ℓ} → Collection ℓ 0 → Set ℓ
Elem      = λ C   → Field 0 C

Carrier   : ∀ {ℓ} → Collection ℓ 0 → Set ℓ
Carrier₁  : ∀ {ℓ} → Collection ℓ 1 → (γ : Set ℓ) → Set ℓ
Carrier₁′ : ∀ {ℓ} {γ : Set ℓ} (C : (Collection ℓ :waist 1) γ) → Set ℓ

Carrier   = λ C   → Field 1 C
Carrier₁  = λ C γ → Field 0 (C γ)
Carrier₁′ = λ C   → Field 0 C

insert   : ∀ {ℓ} (C : Collection ℓ 0) → (Elem C → Carrier C → Carrier C)
insert₁  : ∀ {ℓ} (C : Collection ℓ 1) (γ : Set ℓ) →  γ → Carrier₁ C γ → Carrier₁ C γ
insert₁′ : ∀ {ℓ} {γ : Set ℓ} (C : (Collection ℓ :waist 1) γ) → γ → Carrier₁′ C → Carrier₁′ C

insert    = λ C   → Field 2 C
insert₁   = λ C γ → Field 1 (C γ)
insert₁′  = λ C   → Field 1 C

insert₂  : ∀ {ℓ} (C : Collection ℓ 2) (El Cr : Set ℓ) → El → Cr → Cr
insert₂′ : ∀ {ℓ} {El Cr : Set ℓ} (C : (Collection ℓ :waist 2) El Cr) → El → Cr → Cr

insert₂ = λ C El Cr → Field 0 (C El Cr)
insert₂′ = λ C → Field 0 C

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

Inj₀ : ℕ → Term → Term
Inj₀ zero c    = con (quote inj₁) (arg (arg-info visible relevant) c ∷ [])
Inj₀ (suc n) c = con (quote inj₂) (vArg (Inj₀ n c) ∷ [])

-- Duality!
-- 𝒾-th projection: proj₁ ∘ (proj₂ ∘ ⋯ ∘ proj₂)
-- 𝒾-th injection:  (inj₂ ∘ ⋯ ∘ inj₂) ∘ inj₁

macro
  Inj : ℕ → Term → Term → TC Unit.⊤
  Inj n t goal = unify goal (Inj₀ n t)

macro
  termtype : Term → Term → TC Unit.⊤
  termtype tm goal =
                normalise tm
           >>=ₘ λ tm′ → unify goal (def (quote Fix) ((vArg (Σ→⊎₀ (sources₁ tm′))) ∷ []))

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
PointedOver  : Set → Context (ℓsuc ℓ₀)
PointedOver Ξ    = do Carrier ← Set ℓ₀
                      point   ← Carrier
                      embed   ← (Ξ → Carrier)
                      End {ℓ₀}

ℙ : Set → Set
ℙ X = termtype (PointedOver X :waist 1)

-- Pattern synonyms for more compact presentation
pattern nothingP = μ (inj₁ tt)       -- : ℙ
pattern justP e  = μ (inj₂ (inj₁ e)) -- : ℙ → ℙ

-- Observe that ℙ makes instances of PointdOver!
ℙ-rec : (X : Set) → PointedOver X 0
ℙ-rec X = ⟨ ℙ X , nothingP , justP ⟩

ℙ→Maybe : ∀ {X} → ℙ X → Maybe X
ℙ→Maybe nothingP  = nothing
ℙ→Maybe (justP x) = just x

ℙ←Maybe : ∀ {X} → Maybe X → ℙ X
ℙ←Maybe (just x) = justP x
ℙ←Maybe nothing  = nothingP

ℙ→Maybe∘ℙ←Maybe : ∀ {X} (m : Maybe X) → ℙ→Maybe (ℙ←Maybe m) ≡ m
ℙ→Maybe∘ℙ←Maybe (just x) = refl
ℙ→Maybe∘ℙ←Maybe nothing  = refl

ℙ←Maybe∘ℙ→Maybe : ∀ {X} (p : ℙ X) → ℙ←Maybe (ℙ→Maybe p) ≡ p
ℙ←Maybe∘ℙ→Maybe nothingP  = refl
ℙ←Maybe∘ℙ→Maybe (justP x) = refl
