{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)
open import Level as Level
module Testing_Generated where 


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer MonoidP : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}





{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer M-Set : Set₁ where
   Scalar       : Set
   Vector       : Set
   _·_      : Scalar → Vector → Vector
   𝟙        : Scalar
   _×_      : Scalar → Scalar → Scalar
   leftId       : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc        : ∀ {a b 𝓋} → (a × b) · 𝓋  ≡  a · (b · 𝓋) -}


{- NearRing = M-Set record ⟴ single-sorted "Scalar" -}
record NearRing : Set₁ where
   field Scalar     : Set
   field _·_        : Scalar → Scalar → Scalar
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Scalar}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : ∀ {a b 𝓋} → (a × b) · 𝓋  ≡  a · (b · 𝓋)