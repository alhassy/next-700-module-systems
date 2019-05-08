-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:1]]
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Z-notation for sums
open import Level
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _×_ ; _,_)
Σ∶• : {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Σ∶• = Σ
infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

open import Data.Nat
open import Data.Nat.Properties
-- Facets of Structuring Mechanisms: An Agda Rendition:1 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:2]]
record Monoid-Record : Set₁ where
  infixl 5 _⨾_
  field
    -- Interface
    Carrier  : Set
    Id       : Carrier
    _⨾_      : Carrier → Carrier → Carrier

    -- Constraints
    lid   : ∀{x} → (Id ⨾ x) ≡ x
    rid   : ∀{x} → (x ⨾ Id) ≡ x
    assoc : ∀ x y z → (x ⨾ y) ⨾ z  ≡  x ⨾ (y ⨾ z)

  -- derived result
  pop-Idᵣ : ∀ x y  →  x ⨾ Id ⨾ y  ≡  x ⨾ y
  pop-Idᵣ x y = cong (_⨾ y) rid
  
open Monoid-Record {{...}} using (pop-Idᵣ)
-- Facets of Structuring Mechanisms: An Agda Rendition:2 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:3]]
record HasMonoid (Carrier : Set) : Set₁ where
  infixl 5 _⨾_
  field
    Id    : Carrier
    _⨾_   : Carrier → Carrier → Carrier
    lid   : ∀{x} → (Id ⨾ x) ≡ x
    rid   : ∀{x} → (x ⨾ Id) ≡ x
    assoc : ∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

  pop-Id-tc : ∀ x y →  x ⨾ Id ⨾ y  ≡  x ⨾ y
  pop-Id-tc x y = cong (_⨾ y) rid

open HasMonoid {{...}} using (pop-Id-tc)
-- Facets of Structuring Mechanisms: An Agda Rendition:3 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:4]]
-- Type alias
Monoid-Σ  :  Set₁
Monoid-Σ  =    Σ Carrier ∶ Set 
             • Σ Id ∶ Carrier
             • Σ _⨾_ ∶ (Carrier → Carrier → Carrier)
             • Σ lid ∶ (∀{x} → Id ⨾ x ≡ x) 
             • Σ rid ∶ (∀{x} → x ⨾ Id ≡ x)
             • (∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z))

pop-Id-Σ : ∀{{M : Monoid-Σ}}
                       (let Id  = proj₁ (proj₂ M))
                       (let _⨾_ = proj₁ (proj₂ (proj₂ M)))                       
                   →  ∀ (x y : proj₁ M)  →  (x ⨾ Id) ⨾ y  ≡  x ⨾ y
pop-Id-Σ {{M}} x y = cong (_⨾ y) (rid {x})
                     where  _⨾_    = proj₁ (proj₂ (proj₂ M))
                            rid    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ M))))
-- Facets of Structuring Mechanisms: An Agda Rendition:4 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:5]]
instance
   ℕ-record = record { Carrier = ℕ ; Id = 0 ; _⨾_ = _+_
                     ; lid =  +-identityˡ _  ; rid = +-identityʳ _ ; assoc = +-assoc }

   ℕ-tc : HasMonoid ℕ
   ℕ-tc = record { Id = 0; _⨾_ = _+_
                 ; lid = +-identityˡ _ ; rid = +-identityʳ _ ; assoc = +-assoc }

   ℕ-Σ : Monoid-Σ
   ℕ-Σ = ℕ , 0 , _+_ , +-identityˡ _ , +-identityʳ _ , +-assoc
-- Facets of Structuring Mechanisms: An Agda Rendition:5 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:6]]
ℕ-pop-0ᵣ : ∀ (x y : ℕ) → x + 0 + y  ≡  x + y
ℕ-pop-0ᵣ = pop-Idᵣ

ℕ-pop-0-tc : ∀ (x y : ℕ) → x + 0 + y  ≡  x + y
ℕ-pop-0-tc = pop-Id-tc

ℕ-pop-0ₜ : ∀ (x y : ℕ) → x + 0 + y  ≡  x + y
ℕ-pop-0ₜ = pop-Id-Σ
-- Facets of Structuring Mechanisms: An Agda Rendition:6 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:8]]
-- Following proves: Monoid-Record  ≅  Σ Set HasMonoid.

to-record-from-usual-type : Monoid-Σ → Monoid-Record
to-record-from-usual-type (c , id , op , lid , rid , assoc)
  = record { Carrier = c ; Id = id ; _⨾_ = op
           ; lid = lid ; rid = rid ; assoc = assoc
           } -- Term construed by ‘Agsy’,
             -- Agda's mechanical proof search.

from-record-to-usual-type : Monoid-Record → Monoid-Σ
from-record-to-usual-type M =
  let open Monoid-Record M
  in Carrier , Id , _⨾_ , lid , rid , assoc

  {- Essentially moved from record{⋯} to product listing -}
-- Facets of Structuring Mechanisms: An Agda Rendition:8 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:9]]
module Monoid-Telescope-User
  (Carrier : Set) (Id : Carrier) (_⨾_ : Carrier → Carrier → Carrier)
  (lid   : ∀{x} → Id ⨾ x ≡ x) (rid : ∀{x} → x ⨾ Id ≡ x)
  (assoc : ∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)) 
  where

  pop-Idₘ : ∀(x y : Carrier)  →  (x ⨾ Id) ⨾ y  ≡  x ⨾ y
  pop-Idₘ x y = cong (_⨾ y) (rid {x})
-- Facets of Structuring Mechanisms: An Agda Rendition:9 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:10]]
  record-from-telescope : Monoid-Record
  record-from-telescope
    = record { Carrier = Carrier ; Id = Id ; _⨾_ = _⨾_
             ; lid = lid ; rid = rid ; assoc = assoc }
-- Facets of Structuring Mechanisms: An Agda Rendition:10 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:11]]
module record-to-telescope (M : Monoid-Record) where

  open Monoid-Record M
  -- Treat record type as if it were a parameterised module type,
  -- instantiated with M.

  open Monoid-Telescope-User Carrier Id _⨾_ lid rid assoc
-- Facets of Structuring Mechanisms: An Agda Rendition:11 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:12]]
open Monoid-Telescope-User ℕ 0 _+_ (+-identityˡ _) (+-identityʳ _) +-assoc
-- Facets of Structuring Mechanisms: An Agda Rendition:12 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Facets%20of%20Structuring%20Mechanisms:%20An%20Agda%20Rendition][Facets of Structuring Mechanisms: An Agda Rendition:13]]
ℕ-popₘ  : ∀(x y : ℕ)  →  x + 0 + y  ≡  x + y
ℕ-popₘ  =   pop-Idₘ
-- Facets of Structuring Mechanisms: An Agda Rendition:13 ends here
