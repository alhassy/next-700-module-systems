{- This file is generated ;; do not alter. -}
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as ℓ
module Testing_Generated where 

{- This was generated from the PackageFormer Magma (v : Variation) : Set -}
record Magma (Carrier : Set) : Set (ℓ.suc ℓ.zero) where 
  field
    _⨾_ : Magma v → Magma v → Magma v
    -- Id  : Magma v
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)