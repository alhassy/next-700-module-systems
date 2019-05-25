{- This file is generated ;; do not alter. -}
open import Relation.Binary.PropositionalEquality using (_≡_)
module Generated where
record Semigroup  (Carrier : Set) : Set where
  field
    _⨾_ : Carrier → Carrier → Carrier
    Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
