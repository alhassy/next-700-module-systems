{- This file is generated ;; do not alter. -} 

open import Relation.Binary.PropositionalEquality using (_≡_)
module Testing_Generated where 


{- This was generated from the PackageFormer Magma -}
record MagmaD  (Carrier : Set) : Set where
  field
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- This was generated from the PackageFormer Magma -}
record MagmaR  (Carrier : Set) : Set where
  field
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- This was generated from the PackageFormer Magma -}
record MagmaT  (Carrier : Set) : Set where
  field
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- This was generated from the PackageFormer Magma -}
record Magma-typeclass  (Carrier : Set) : Set where
  field
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)