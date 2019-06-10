{- This file is generated ;; do not alter. -}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as ℓ
module Testing_Generated where 

{- This was generated from the PackageFormer Magma -}
record Magma-typeclass (Carrier : Set) : Set (ℓ.suc ℓ.zero)where
  field
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- This was generated from the PackageFormer Magma -}
record MagmaT (Carrier : Set) : Set (ℓ.suc ℓ.zero)where
  field
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- This was generated from the PackageFormer Magma -}
record MagmaR  : Set (ℓ.suc ℓ.zero)where
  field
    Carrier : Set
    _⨾_ : Carrier → Carrier → Carrier
    -- Id  : Carrier
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

{- This was generated from the PackageFormer Magma -}
data MagmaD  : Set (ℓ.suc ℓ.zero)where
    _⨾_ : MagmaD → MagmaD → MagmaD
    -- Id  : MagmaD

{- This was generated from the PackageFormer Graph -}
record AGraph (Carrier : Set) : Set (ℓ.suc ℓ.zero)where
  field
    Vertex : Set
    _⟶_ : Vertex → Vertex → Set