{- This file is generated ;; do not alter. -}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as ℓ
module Testing_Generated where 

{- SemigroupTypeclass = Semigroup typeclass -}
record SemigroupTypeclass (Carrier : Set) : Set (ℓ.suc ℓ.zero) where
  field
    _⨾_ : Carrier → Carrier → Carrier
    Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- SemigroupT = Semigroup typeclass -}
record SemigroupT (Carrier : Set) : Set (ℓ.suc ℓ.zero) where
  field
    _⨾_ : Carrier → Carrier → Carrier
    Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- SemigroupR = Semigroup record -}
record SemigroupR : Set (ℓ.suc ℓ.zero) where
  field
    Carrier : Set
    _⨾_ : Carrier → Carrier → Carrier
    Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- SemigroupD = Semigroup data -}
data SemigroupD : Set (ℓ.suc ℓ.zero) where
    _⨾_ : SemigroupD → SemigroupD → SemigroupD
    Id  : SemigroupD