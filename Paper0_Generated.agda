{- This file is generated ;; do not alter. -}

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List hiding (concat)
open import Level as Level
module Paper0_Generated where 


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidPⁱᵈ = MonoidP identity -}
PackageFormer MonoidPⁱᵈ : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidP⁰  = MonoidP -}
PackageFormer MonoidP⁰ : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidPᶜ = MonoidP ⟴ -}
PackageFormer MonoidPᶜ : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Monoid₀′ = MonoidP record -}
record Monoid₀′ : Set₁ where
  field
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoid₁″ = MonoidP record ⟴ :waist 1 -}
record Monoid₁″ (Carrier : Set) : Set₁ where
  field
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoid₂″ = MonoidP record ⟴ :waist 2 -}
record Monoid₂″ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set₁ where
  field
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoid₃′ = MonoidP termtype :carrier "Carrier" -}
data Monoid₃′ : Set where
    _⨾_ : Monoid₃′ → Monoid₃′ → Monoid₃′
    Id : Monoid₃′


{- Monoid₄ = MonoidP termtype-with-variables :carrier "Carrier" -}
data Monoid₄ (Varsg14282 : Set) : Set where
    inj : Varsg14282 → Monoid₄ Varsg14282
    _⨾_ : Monoid₄ Varsg14282 → Monoid₄ Varsg14282 → Monoid₄ Varsg14282
    Id : Monoid₄ Varsg14282





{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer MonoidPE : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    Lid : Carrier → Carrier
    Lid x = Id ⨾ x
    Rid : Carrier → Carrier
    Rid x = x ⨾ Id
    concat : List Carrier → Carrier
    concat = foldr _⨾_ Id
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → Rid x ≡ x
    Id² : Id ⨾ Id ≡ Id
    Id² = rightId
    concatₚ : List Carrier → Carrier
    concatₚ []       = Id
    concatₚ (x ∷ xs) = x ⨾ concatₚ xs -}


{- Monoid⁰ = MonoidPE decorated :by "⁰" ⟴ recordₑ -}
record Monoid⁰ : Set₁ where
  field Carrier⁰ : Set
  field _⨾⁰_     : Carrier⁰ → Carrier⁰ → Carrier⁰
  field Id⁰      : Carrier⁰
  Lid⁰ : Carrier⁰ → Carrier⁰ ; Lid⁰ x = Id⁰ ⨾⁰ x
  Rid⁰ : Carrier⁰ → Carrier⁰ ; Rid⁰ x = x ⨾⁰ Id⁰
  concat⁰ : List Carrier⁰ → Carrier⁰ ; concat⁰ = foldr _⨾⁰_ Id⁰
  field leftId⁰  : ∀ {x : Carrier⁰} → Id⁰ ⨾⁰ x ≡ x
  field rightId⁰ : ∀ {x : Carrier⁰} → Rid⁰ x ≡ x
  Id²⁰ : Id⁰ ⨾⁰ Id⁰ ≡ Id⁰ ; Id²⁰ = rightId⁰
  concatₚ⁰ : List Carrier⁰ → Carrier⁰ ; concatₚ⁰ []       = Id⁰ ; concatₚ⁰ (x ∷ xs) = x ⨾⁰ concatₚ⁰ xs


{- Monoid₆ = MonoidPE termtype :carrier "Carrier" ⟴ decorated :by "₆" -}
data Monoid₆ : Set where
    _⨾₆_ : Monoid₆ → Monoid₆ → Monoid₆
    Id₆ : Monoid₆
    Lid₆ : Monoid₆ → Monoid₆
    Rid₆ : Monoid₆ → Monoid₆
    concat₆ : List Monoid₆ → Monoid₆
    concatₚ₆ : List Monoid₆ → Monoid₆


{- Monoid³ = MonoidPE decorated :by "³" ⟴ termtypeₑ :carrier "Carrier³" -}
data Monoid³ : Set where
    _⨾³_ : Monoid³ → Monoid³ → Monoid³
    Id³ : Monoid³
Lid³ : Monoid³ → Monoid³ ; Lid³ x = Id³ ⨾³ x
Rid³ : Monoid³ → Monoid³ ; Rid³ x = x ⨾³ Id³
concat³ : List Monoid³ → Monoid³ ; concat³ = foldr _⨾³_ Id³
concatₚ³ : List Monoid³ → Monoid³ ; concatₚ³ []       = Id³ ; concatₚ³ (x ∷ xs) = x ⨾³ concatₚ³ xs