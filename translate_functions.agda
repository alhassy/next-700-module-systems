-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:1]]
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Z-notation for sums
open import Level
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _×_ ; _,_)
Σ∶• : {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Σ∶• = Σ
infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B
-- Missing Features:1 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:2]]
-- One extreme: Completely bundled up
record Semigroup0 : Set₁ where
  field 
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    assoc   : ∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
-- Missing Features:2 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:3]]
-- ‘Typeclass’ on a given Carrier
-- Alternatively: Carrier is known as runtime.
record Semigroup1 (Carrier : Set): Set₁ where
  field 
    _⨾_   : Carrier → Carrier → Carrier
    assoc : ∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
-- Missing Features:3 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:4]]
-- Two items known at run time --c.f., “IsSemi” above.
record Semigroup2
 (Carrier : Set)
 (_⨾_     : Carrier → Carrier → Carrier) : Set where
  field 
    assoc : ∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
-- Missing Features:4 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:5]]
-- A value of “Semigroup3 C op pf” is trivially the empty record, if any,
-- provided ‘pf’ is a proof that ‘C’ forms a semigroup with ‘op’.
-- This type is usualy written “Σ C ∶ Set • Σ _⨾_ ∶ C → C → C • Σ assoc ∶ ⋯”.
record Semigroup3
 (Carrier : Set) 
 (_⨾_ : Carrier → Carrier → Carrier)
 (assoc : ∀ x y z → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)) : Set where
  -- no fields
-- Missing Features:5 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:6]]
Surjection : ∀{A B : Set} → (A → B) → Set
Surjection {A} {B} f = ∀ (b : B) → Σ a ∶ A • b ≡ f a
-- (Σ a ∶ A • P a) ≈ { (a, proof) ❙ a ∈ A ∧ pf is a proof of P(a) }

Injection : ∀{A B : Set} → (A → B) → Set
Injection {A} {B} f = ∀ {x y} →  f x ≡ f y → x ≡ y
-- Missing Features:6 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:7]]
translate1 : ∀{A B} → (f : A → B) → Surjection f → Injection f → Semigroup1 A → Semigroup1 B
translate1 f surj inj AS =
  let
    open Semigroup1 AS

    -- x ⨾′ y is obtained by applying f to the ⨾-composition of the pre-images of x and y.
    infix 5 _⨾′_
    _⨾′_ = λ x y → let a0 = proj₁ (surj x); a1 = proj₁ (surj y) in f (a0 ⨾ a1)

    -- f distributes over ⨾ turning it into ⨾′.
    factor : ∀ {a a′} → f a ⨾′ f a′ ≡ f (a ⨾ a′)
    factor {a} {a′} =
               let 𝒶  , m  = surj (f a)
                   𝒶′ , w  = surj (f a′)
               in    
               begin
                 f a ⨾′ f a′
               ≡⟨ refl ⟩
                 f (𝒶 ⨾ 𝒶′)
               ≡⟨ cong f (cong₂ _⨾_ (inj (sym m)) (inj (sym w)))  ⟩
                 f (a ⨾ a′)
               ∎

    distribute : ∀ {a a′} → f (a ⨾ a′) ≡ f a ⨾′ f a′
    distribute {a} {a′} = sym (factor {a} {a′})
    
  in -- Bundle up ⨾′ along with a proof of associtivity 
    record { _⨾_ = _⨾′_; assoc = λ x y z → 
     let
        -- Obtain f-pre-images
        a₀ , x≈fa₀  =  surj x
        a₁ , y≈fa₁  =  surj y
        a₂ , z≈fa₂  =  surj z
     in
      {- Tersely, we rewrite along the pre-images,
         factor f, perform the associativity of ⨾,
         then distribute f and rewrite along the pre-images.
      -}
       begin
         (x ⨾′ y) ⨾′ z
       ≡⟨ cong₂ _⨾′_ (cong₂ _⨾′_ x≈fa₀ y≈fa₁) z≈fa₂ ⟩
         (f a₀ ⨾′ f a₁) ⨾′ f a₂
       ≡⟨ cong (_⨾′ f a₂) factor ⟩
         f (a₀ ⨾ a₁) ⨾′ f a₂
       ≡⟨ factor ⟩
         f ((a₀ ⨾ a₁) ⨾ a₂)
       ≡⟨ cong f (assoc _ _ _)  ⟩
         f (a₀ ⨾ (a₁ ⨾ a₂))
       ≡⟨ distribute ⟩
         f a₀ ⨾′ f (a₁ ⨾ a₂)
       ≡⟨ cong (f a₀ ⨾′_) distribute ⟩
         f a₀ ⨾′ (f a₁ ⨾′ f a₂)
       ≡⟨ sym (cong₂ _⨾′_ x≈fa₀ (cong₂ _⨾′_ y≈fa₁ z≈fa₂))  ⟩
         x ⨾′ (y ⨾′ z)
       ∎
  }
-- Missing Features:7 ends here

-- [[file:~/thesis-proposal/thesis-proposal.org::*Missing%20Features][Missing Features:8]]
translate0 : ∀{B : Set} (AS : Semigroup0) (f : Semigroup0.Carrier AS → B)
           → Surjection f → Injection f
           → Semigroup0
translate0 {B} AS f surj inj = record { Carrier = B ; _⨾_ = _⨾_ ; assoc = assoc }
  where

       -- Repackage ‘AS’ from a ‘Semigroup0’ to a ‘Semigroup1’
       -- only to immediatley unpack it, so that its contents
       -- are available to be repacked above as a ‘Semigroup0’.
      
       pack : Semigroup1 (Semigroup0.Carrier AS)
       pack = let open Semigroup0 AS
               in record {_⨾_ = _⨾_; assoc = assoc }

       open Semigroup1 (translate1 f surj inj pack)
-- Missing Features:8 ends here
