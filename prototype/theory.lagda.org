#+title: Progressing on a type theory for =PackageFormer=
#+author: Musa Al-hassy
#+agda_version: 2.6.0.1

MA: In the setup below, it seems using the context approach can sometimes be easier
than using the λ approach, even though they are essentially the same.
Intuitively:
| What doing? | Easier to use |
|-------------+---------------|
| Reasoning   | Context       |
| Programming | Functions     |

* Imports
#+BEGIN_SRC agda2
module pf where

open import Level renaming (zero to ℓzero; suc to ℓsuc; _⊔_ to _⊍_)
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

#+END_SRC

* Syntax Declarations
#+BEGIN_SRC agda2

Name = String

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

infixr 10 Π
syntax Π A (λ x → B) = Π x ∶ A • B

infix 9 _⊢Term_

#+END_SRC
* Contexts, types, and terms

  Contexts are types, level-indexed types are functions, τ-terms are functions taking
  the context and yielding a value.


 #+BEGIN_SRC agda2
PackageFormer : (i : Level) → Set (ℓsuc i)
PackageFormer i = Set i
#+END_SRC

** types
 Next, object-level universes are implemented using meta-level universes.
 - Note: =Γ ⊢Type 𝒾  ≡  Γ ⊢Term (𝒰 𝒾)=.

 #+BEGIN_SRC agda2
_⊢Type_ :  ∀ {i} → PackageFormer i → (j : Level) → Set (i ⊍ ℓsuc j)
Γ ⊢Type 𝒾 = Γ → Set 𝒾

𝒰 : ∀ {i} {Γ : PackageFormer i} (j : Level) → Γ ⊢Type (ℓsuc j)
𝒰 j = λ γ → Set j
 #+END_SRC
** terms
 #+BEGIN_SRC agda2
_⊢Term_ : ∀ {i j} → (Γ : PackageFormer i) → Γ ⊢Type j → Set (i ⊍ j)
Γ ⊢Term τ = (γ : Γ) → τ γ
 #+END_SRC

 After all, a classical context ~x₁ : τ₁, …, xₙ : τₙ ⊢ e : τ~ only /asserts/ =e : τ=
 /provided/ =xᵢ : τᵢ=, and so the latter is a function of the former! Indeed, as the
 λ-introduction rule shows, *all contexts are the humble function*
 ---e.g., with church encodings, we have that algebraic data-types are also
 functions, the eliminators.
 + MA: Perhaps with this neato observation, I should simply focus on functions?

** context constructors

 The empty context is the unit type and context extension is interpreted using Σ-types.
 The identity of dependent products is the unit type, whence it denotes the empty PackageFormer.

#+BEGIN_SRC agda2
ε : PackageFormer ℓzero
ε = ⊤

_▷_ : ∀ {i j} (Γ : PackageFormer i) → Γ ⊢Type j → PackageFormer (i ⊍ j)
Γ ▷ A = Σ γ ∶ Γ • A γ

 #+END_SRC
* Coercisions and Π

#+BEGIN_SRC agda2
weaken : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type k}
       → Γ ⊢Type j → (Γ ▷ A) ⊢Type j
weaken τ (γ , a) = τ γ

pf-refl : ∀ {i j} {Γ : PackageFormer i} {A : Γ ⊢Type j}
        → (Γ ▷ A) ⊢Term weaken A
pf-refl = proj₂

Π : ∀ {i j k} {Γ : PackageFormer i} (A : Γ ⊢Type j) (B : (Γ ▷ A) ⊢Type k)
  → Γ ⊢Type (j ⊍ k)
Π A B = λ γ → ∀ (a : A γ) → B (γ , a)

_⇒_ : ∀ {i j k} {Γ : PackageFormer i} (A : Γ ⊢Type j) (B : Γ ⊢Type k)
    → Γ ⊢Type (j ⊍ k)
A ⇒ B = Π A (weaken B)

#+END_SRC
* =lam= and =app=
Abstraction and application are just Currying & Uncurrying
#+BEGIN_SRC agda2
lam : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type j} {B : (Γ ▷ A) ⊢Type k}
    → (Γ ▷ A) ⊢Term B  →  Γ ⊢Term (Π A B)
lam g = λ γ → λ a → g (γ , a)

app : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type j} {B : (Γ ▷ A) ⊢Type k}
      →  Γ ⊢Term (Π A B)  → (Γ ▷ A) ⊢Term B
app g = λ{(γ , a) → g γ a}
#+END_SRC

Here are other forms of function application.
#+BEGIN_SRC agda2
cut′ : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type j} {B : Γ ⊢Type k}
      →  (Γ ▷ A) ⊢Term weaken B
      →  Γ       ⊢Term A
      →  Γ       ⊢Term B
cut′ f a = λ γ → f (γ , a γ)

_on_ : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type j}
      → (Γ ▷ A) ⊢Type k
      →  Γ ⊢Term A
      →  Γ ⊢Type k
f on a = λ γ → f (γ , a γ)

cut : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type j} {B : (Γ ▷ A) ⊢Type k}
      →  (Γ ▷ A) ⊢Term B
      →  (a : Γ  ⊢Term A)
      →  Γ       ⊢Term (B on a)
cut f a = λ γ → f (γ , a γ)

_$_ : ∀ {i j k} {Γ : PackageFormer i} {A : Γ ⊢Type j} {B : (Γ ▷ A) ⊢Type k}
      → Γ ⊢Term (Π A B)
      → (a : Γ ⊢Term A)
      → Γ ⊢Term (B on a)
_$_ g = λ a γ → g γ (a γ)
#+END_SRC

* Example terms!

#+BEGIN_SRC agda2
‵id : ε ⊢Term Π A ∶ 𝒰 ℓzero • let A′ = λ _ → proj₂ A -- weakening.
                              in (A′ ⇒ A′) ε
‵id = lam (lam proj₂)
#+END_SRC

Let's try to show that =pf-refl= really is the identity function, up to isomorphism.
#+BEGIN_SRC agda2
‵id₂ : ∀ {i j} {Γ : PackageFormer i} {A : Γ ⊢Type j}
     → Γ ⊢Term A ⇒ A
‵id₂ = lam pf-refl
#+END_SRC

Neato! Progress, finally (งಠ_ಠ)ง
* Old Approach using Deep Embedding :incomplete:holes:

  #+begin_example agda2
module pf where
#+end_example
** Imports
#+begin_example agda2
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
#+end_example
** Fixity & syntax declarations
#+begin_example agda2
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
#+end_example
** Declarations for mutually recursive DTL concepts
#+begin_example agda2
data PF : Set                          -- Syntax of PackageFormers; i.e., contexts
data _⊢Type (Γ : PF) : Set             -- Types in context
type-names-of : PF → List Name
-- types-of : (Γ : PF) → List (Γ ⊢Type)   -- The collection of types mentioned in a context
record _⊢constituent (Γ : PF) : Set    -- The type of terms
data _⊢Term:_ (Γ : PF) : Γ ⊢Type → Set -- Terms in context
#+end_example
** PackageFormer syntax
#+begin_example agda2
data PF where
  empty : PF
  _extended-by_ : (Γ : PF) → Γ ⊢constituent → PF
#+end_example
** “declarations in context”
#+begin_example agda2
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
#+end_example
** Decision procedure for tedious proofs
#+begin_example agda2
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
#+end_example
** “types in context”
#+begin_example agda2
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
#+end_example
** =type-names-of=
#+begin_example agda2
type-names-of empty = []
type-names-of (pf extended-by name₁ ∶ ‵Set) = name₁ ∷ type-names-of pf
type-names-of (pf extended-by _) = type-names-of pf
#+end_example
** A hierarchy of dependent weakening rules
#+begin_example agda2
{-
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
#+end_example
** How many ‘arguments’ does a type have?
#+begin_example agda2
{-

arity : ∀ {Γ} → Γ ⊢Type → ℕ
arity ‵Set        = 0
arity (‵∀ τ body) = 1 + arity (body "_") -- Hack; possible since names are strings.
arity (τ ‵→ τ₁)   = 1 + arity γ  -- E.g., α ‵→ (β ‵→ γ) has 2 arguments.
arity (‵ η)       = {!!} -- Need to consider its type in Γ
arity (eq τ l r)  = 0
-}
#+end_example
** The subparts of a type expression
#+begin_example agda2
{--

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
#+end_example
** “terms in context”
#+begin_example agda2
data _⊢Term:_ Γ where

  -- TODO: “x must be fresh for Γ”; variable case
  ‵_  : {τ : Γ ⊢Type} (x : Name) → Γ ⊢Term: τ

  -- curried function application
  -- _$_ : (f : Γ ⊢constituent) → type-head (type f) → Γ ⊢Term: type-tail (type f) -- Omitted for brevity
#+end_example
** Examples
#+begin_example agda2
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
#+end_example
** Semantics
#+begin_example agda2
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

#+end_example
** Further experiments
#+begin_example agda2
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
  #+end_example
