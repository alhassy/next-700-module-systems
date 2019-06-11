module Testing where
open import Testing_Generated
open import Level as ℓ

{-700
PackageFormer Semigroup (v : Variation) : Set (ℓ.suc ℓ.zero) where
  field
    _⨾_ : Semigroup v → Semigroup v → Semigroup v
    Id  : Semigroup v
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

SemigroupTypeclass = Semigroup typeclass
SemigroupT = Semigroup typeclass
SemigroupR = Semigroup record
SemigroupD = Semigroup data
-}

_ = SemigroupTypeclass
_ = SemigroupT
_ = SemigroupR
_ = SemigroupD
