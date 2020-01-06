module pf where

--------------------------------------------------------------------------------
-- Imports

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String) renaming (_==_ to _==ₛ_; _≟_ to _≟ₛ_; _++_ to _++ₛ_)
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _×_ ; _,_)
Name = String

--------------------------------------------------------------------------------
-- Fixity & syntax declarations

infix 11 eq
syntax eq τ l r  =  l ‵≡ r ∶ τ

infixr 10 _‵→_ ‵∀
syntax ‵∀ τ (λ η → γ) = Π η ∶ τ • γ -- “Z-notation”

-- infixl 9 _∶_ _∶_≔_
infixl 9 _∶_

infixl 5 _extended-by_

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

--------------------------------------------------------------------------------

type-names-of empty = []
type-names-of (pf extended-by name₁ ∶ ‵Set) = name₁ ∷ type-names-of pf
type-names-of (pf extended-by _) = type-names-of pf

--------------------------------------------------------------------------------
-- Declarations for mutually recursive DTL concepts

data PF : Set                          -- Syntax of PackageFormers; i.e., contexts
data _⊢Type (Γ : PF) : Set             -- Types in context
type-names-of : PF → List Name
-- types-of : (Γ : PF) → List (Γ ⊢Type)   -- The collection of types mentioned in a context
record _⊢constituent (Γ : PF) : Set    -- The type of terms
data _⊢Term:_ (Γ : PF) : Γ ⊢Type → Set -- Terms in context

--------------------------------------------------------------------------------
-- PackageFormer syntax

data PF where
  empty : PF
  _extended-by_ : (Γ : PF) → Γ ⊢constituent → PF

--------------------------------------------------------------------------------
-- “declarations in context”

record _⊢constituent Γ where
  -- constructor _∶_≔_
  constructor _∶_
  inductive
  field
    name     : Name
    type     : Γ ⊢Type
    -- equation : Maybe (Γ ⊢Term: type)
    -- Ommitted for brevity

open _⊢constituent

{-
_∶_ : ∀ {Γ} → Name → Γ ⊢Type → Γ ⊢constituent
x ∶ τ = x ∶ τ ≔ nothing
-}

--------------------------------------------------------------------------------
-- Soundness: Let's construct a decision procedure that actually provides tedious proofs.
-- This is used in the ADT “_⊢Type”.

data Error : String → Set where

present? : Name → List Name → Set
present? η []       = Error ("The type “" ++ₛ η ++ₛ "” is not in the parent context!")
present? η (n ∷ ns) with η ==ₛ n
...| true  = ⊤
...| false = present? η ns

soundness : ∀ {η ns} → present? η ns → η ∈ ns
soundness {η} {n ∷ ns} p with η ≟ₛ n
...| yes q = here q
...| no ¬q = there (soundness p)

tedious-example : "C" ∈ ("A" ∷ "B" ∷ "C" ∷ "D" ∷ [])
tedious-example = there (there (here refl))

improved-example : "C" ∈ ("A" ∷ "B" ∷ "C" ∷ "D" ∷ [])
improved-example = soundness tt

-- Uncomment to see an error since c is not in the list.
-- useful-error-msg : "c" ∈ ("A" ∷ "B" ∷ "C" ∷ "D" ∷ [])
-- useful-error-msg = soundness tt

--------------------------------------------------------------------------------
-- “types in context”

{-
  τ ∷= Set       “universe of types”
     | τ → τ     “function types”
     | α         “atomic types mentioned in the context”
     | e ≡ d     “term equality in context”
-}

data _⊢Type Γ where

  ‵Set  : Γ ⊢Type                                        -- type of small types

  -- ‵∀ : (τ : Γ ⊢Type) (body : Γ ⊢Term: τ → Γ ⊢Type) → Γ ⊢Type -- Pi types, we fail the positivity checker.
  -- In the spirit of gradual typing, we use a weaker form: The assumed term losses any possible definiens, equations.
  ‵∀ : (τ : Γ ⊢Type) (body : (η : Name) → (Γ extended-by η ∶ τ) ⊢Type) → Γ ⊢Type

  _‵→_ : Γ ⊢Type → Γ ⊢Type → Γ ⊢Type -- function type; making this derived requires a weak form of commuatvity at the context level

  -- variable case; the name must be mentioned in Γ
  ‵_   : (η : Name) {{_ : present? η (type-names-of Γ)}} → Γ ⊢Type

  eq : (τ : Γ ⊢Type) (l r : Γ ⊢Term: τ) → Γ ⊢Type

{-
_‵→_ : {Γ : PF} → Γ ⊢Type → Γ ⊢Type → Γ ⊢Type -- function type
τ ‵→ γ = Π _ ∶ τ • weaken γ
-}

--------------------------------------------------------------------------------
{- A hierarchy of dependent weakening rules.

weaken1 : ∀ {Γ e} → Γ ⊢Type → (Γ extended-by e) ⊢Type

insert-before-last : ∀ {Γ η e τ} → (Γ extended-by η ∶ τ) ⊢Type
                                 → (Γ extended-by e extended-by η ∶ weaken1 τ) ⊢Type

insert-before-second-last : ∀ {Γ η₁ η₂ τ₁ τ₂ e}
 → (Γ extended-by               η₁ ∶         τ₁ extended-by η₂ ∶  τ₂) ⊢Type
 → (Γ extended-by e extended-by η₁ ∶ weaken1 τ₁ extended-by η₂ ∶ insert-before-last τ₂) ⊢Type
insert-before-second-last τ = {!!}

insert-before-last ‵Set = ‵Set
insert-before-last (‵∀ τ body) = Π η ∶ insert-before-last τ •  insert-before-second-last (body η)
insert-before-last (τ ‵→ τ₁) = {!!}
insert-before-last (‵ η) = {!!}
insert-before-last (eq τ l r) = {!!}

weaken1 ‵Set        = ‵Set
weaken1 (‵∀ τ body) = Π η ∶ weaken1 τ • insert-before-last (body η)
weaken1 (τ ‵→ τ₁)   = {!!}
weaken1 (‵ η)       = {!!}
weaken1 (eq τ l r)  = {!!}
-}

{- Other weakening rules
weaken-cons : ∀ {Γ e} → Γ ⊢constituent → (Γ extended-by e) ⊢constituent

weaken-mid : ∀ {Γ pre post new} → (Γ extended-by pre extended-by post) ⊢Type
                                → (Γ extended-by pre extended-by new extended-by weaken-cons post) ⊢Type
-}

--------------------------------------------------------------------------------
{-- How many ‘arguments’ does a type have?

arity : ∀ {Γ} → Γ ⊢Type → ℕ
arity ‵Set        = 0
arity (‵∀ τ body) = 1 + arity (body "_") -- Hack; possible since names are strings.
arity (τ ‵→ τ₁)   = 1 + arity γ  -- E.g., α ‵→ (β ‵→ γ) has 2 arguments.
arity (‵ η)       = {!!} -- Need to consider its type in Γ
arity (eq τ l r)  = 0
-}

--------------------------------------------------------------------------------
{-- The subparts of a type expression

-- An alias for _≡_; a singleton type
data JustThis {A : Set} : A → Set where
  this : (a : A) → JustThis a

-- If arity τ = 0 then ⊤ else the type of the first argument.
type-head : ∀ {Γ} → Γ ⊢Type → Set
type-head ‵Set      = ⊤
type-head (τ ‵→ _)  = JustThis τ
type-head _  = ⊤

-- If arity τ = 0 then ⊤ else the type of the first argument.
type-tail : ∀ {Γ} → Γ ⊢Type → Γ ⊢Type
type-tail τ = {!!}
-}

--------------------------------------------------------------------------------
-- “terms in context”

data _⊢Term:_ Γ where

  -- TODO: “x must be fresh for Γ”; variable case
  ‵_  : {τ : Γ ⊢Type} (x : Name) → Γ ⊢Term: τ

  -- curried function application
  -- _$_ : (f : Γ ⊢constituent) → type-head (type f) → Γ ⊢Term: type-tail (type f) -- Omitted for brevity

-----------------------------------------------------------------------------------------
-- Examples

Type : PF
Type = empty extended-by "Carrier" ∶ ‵Set

Indistinguishable : PF
Indistinguishable = Type extended-by
                         "blind" ∶ Π 𝓁 ∶ ‵ "Carrier" • Π 𝓇 ∶ ‵ "Carrier" • ‵ 𝓁 ‵≡ ‵ 𝓇 ∶ ‵ "Carrier"

Pointed : PF
Pointed = Type extended-by "𝟙" ∶ ‵ "Carrier"
-- Typos such as forgetting the final letter produce type-checking errors:
-- The type “Carrie” is not in the parent context!
-- Pointed = Type extended-by "𝟙" ∶ ‵ "Carrie"

Magma : PF
Magma = Type extended-by "_·_" ∶ ‵ "Carrier" ‵→ ‵ "Carrier" ‵→ ‵ "Carrier"

--------------------------------------------------------------------------------
-- Semantics

terms : PF → List (Σ Γ ∶ PF • Γ ⊢constituent)
terms empty = []
terms (p extended-by x) = terms p ++ [ p , x ]

Type-names-of : PF → Set
Type-names-of Γ = Σ η ∶ Name • present? η (type-names-of Γ)

semₜ : ∀ {Γ} → (Type-names-of Γ → Set₁) → Γ ⊢Type → Set₂
semₑ : ∀ {Γ} {τ : Γ ⊢Type} (σ : Type-names-of Γ → Set₁) → Γ ⊢Term: τ → Set₁ -- semₜ σ τ  ⇐  free variables are just placeholders for the types they represent

semₑ {Γ} {τ} σ (‵ x) = {!semₜ σ τ!}

open import Level using (Lift)

semₜ σ ‵Set          = Set₁
semₜ σ (‵∀ τ body)   = ∀ (x : semₜ σ τ) → ⊥ -- TODO
semₜ σ (τ ‵→ γ)      = semₜ σ τ → semₜ σ γ
semₜ σ (‵_ η {{p}})  = Lift _ (σ (η , p))
semₜ σ (eq τ l r)    = semₑ σ l ≡ semₑ σ r  -- ARGH: semₑ must yield Set₁ so it can be used in semₜ !!!!!!  -- JC, what do?

{-
present?-tn : ∀ {η Γ e} →   present? η (type-names-of (Γ extended-by e))
                          ≡ (if   (η ==ₛ name e)
                             then ⊤
                             else present? η (type-names-of Γ))
present?-tn {η} {Γ} {e} with type-names-of (Γ extended-by e) | η ==ₛ name e
present?-tn {η} {Γ} {e} | [] | false = {!!}
present?-tn {η} {Γ} {e} | [] | true = {!!}
present?-tn {η} {Γ} {e} | x ∷ xs | t = {!!}


weaken-present? : ∀ {η Γ e} → present? η (type-names-of Γ)
                            → present? η (type-names-of (Γ extended-by e))
weaken-present? {η} {Γ = Γ} p with type-names-of Γ | p
weaken-present? {η} {Γ = Γ} p | x ∷ xs | q with η ==ₛ x
weaken-present? {η} {Γ} p | x ∷ xs | q | false = {!!}
weaken-present? {η} {Γ} p | x ∷ xs | q | true = {!!}
-}

weaken : ∀ {Γ e}  → Γ ⊢Type → (Γ extended-by e) ⊢Type
weaken ‵Set        = ‵Set
weaken (‵∀ τ body) = {!!}
weaken (τ ‵→ γ)   = weaken τ ‵→ weaken γ
weaken (‵_ η {{p}})       = ‵_ η {{{!!}}}
weaken (eq τ l r)  = {!!}

terms′ : (Γ : PF) (σ : Γ ⊢Type → Set) → List (Σ Γ′ ∶ PF • Set × Γ′ ⊢constituent)
terms′ empty σ = []
terms′ (p extended-by e@(η ∶ τ)) σ = terms′ p (λ x → σ (weaken x)) ++ [ p , σ (weaken τ) , e ] -- terms′ p {!!} ++ [ p , {!!} , {!x!} ]
-- terms p ++ [ p , x ]


{-
sem : (Γ : PF) (σ : Γ ⊢Type → Set) (α : (η : Name) → Σ T ∶ Set • T) → Set
sem p σ α with terms p
...| [] = ⊥
...| (_ , η ∶ τ) ∷ xs = {!!}
  where -- function patching
        α′ : Name → Σ T ∶ Set • T
        α′ n = if n ==ₛ η then (σ {!!}) , {!!} else α n
-}

--------------------------------------------------------------------------------
-- Further experiments

{-
-- TODO: Add support for catenating PFs.
--
-- _⌢_ : PF → PF → PF
-- l ⌢ empty = l
-- l ⌢ (r extended-by x) = (l ⌢ r) extended-by {! need a weakening rule!}
--

monoid : PF
monoid = empty extended-by "Carrier" ∶ ‵Set
               extended-by "_·_" ∶ ‵ "Carrier" ‵→ ‵ "Carrier" ‵→ ‵ "Carrier"
               extended-by "𝟙" ∶ ‵ "Carrier"
               extended-by "assoc" ∶ {!!}
-}
