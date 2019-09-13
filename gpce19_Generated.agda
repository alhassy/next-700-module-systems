{- This file is generated ;; do not alter. -}

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List hiding (concat)
open import Level as Level
module gpce19_Generated where 


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer MonoidP : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidPⁱᵈ = MonoidP identity -}
PackageFormer MonoidPⁱᵈ : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidP⁰  = MonoidP -}
PackageFormer MonoidP⁰ : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidPᶜ = MonoidP ⟴ -}
PackageFormer MonoidPᶜ : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Monoid₀′ = MonoidP record -}
record Monoid₀′ : Set₁ where
    field Carrier       : Set
    field _⨾_       : Carrier → Carrier → Carrier
    field Id        : Carrier
    field assoc     : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    field leftId        : ∀ {x : Carrier} → Id ⨾ x ≡ x
    field rightId       : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoid₁″ = MonoidP record ⟴ :waist 1 -}
record Monoid₁″ (Carrier : Set) : Set₁ where
    field _⨾_       : Carrier → Carrier → Carrier
    field Id        : Carrier
    field assoc     : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    field leftId        : ∀ {x : Carrier} → Id ⨾ x ≡ x
    field rightId       : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoid₂″ = MonoidP record ⟴ :waist 2 -}
record Monoid₂″ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set₁ where
    field Id        : Carrier
    field assoc     : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    field leftId        : ∀ {x : Carrier} → Id ⨾ x ≡ x
    field rightId       : ∀ {x : Carrier} → x ⨾ Id ≡ x





{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer MonoidPE : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    Lid     : Carrier → Carrier ;   Lid x = Id ⨾ x
    Rid     : Carrier → Carrier ;   Rid x = x ⨾ Id
    concat      : List Carrier → Carrier ;  concat = foldr _⨾_ Id
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → Rid x ≡ x
    Id²     : Id ⨾ Id ≡ Id ;    Id² = rightId
    concatₚ     : List Carrier → Carrier ;  concatₚ []       = Id ; concatₚ (x ∷ xs) = x ⨾ concatₚ xs -}


{- Monoid-woah = MonoidPE termtype "Carrier" :discard-only-equations t -}
data Monoid-woah : Set where
    _⨾_     : Monoid-woah → Monoid-woah → Monoid-woah
    Id      : Monoid-woah
    Lid     : Monoid-woah → Monoid-woah
    Rid     : Monoid-woah → Monoid-woah
    concat      : List Monoid-woah → Monoid-woah
    concatₚ     : List Monoid-woah → Monoid-woah