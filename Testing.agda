-- (parse-700-comments)
-- instantiations-remaining
-- package-formers

module Testing where
open import Testing_Generated
open import Level as ℓ

{-700
PackageFormer Magma (v : Variation) : Set (ℓ.suc ℓ.zero) where
  field
    _⨾_ : Magma v → Magma v → Magma v
    -- Id  : Magma v
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

Magma-typeclass = Magma typeclass
-}

{-
MagmaT = Magma typeclass
MagmaR = Magma record
MagmaD = Magma data
-}

{-
_ = MagmaD
_ = MagmaR
_ = MagmaT
_ = Magma-typeclass
-}

{-00

PackageFormer Graph (v : Variation) : Set (ℓ.suc ℓ.zero) where
  field
    Vertex : Set
    _⟶_ : Vertex → Vertex → Set

AGraph = Graph typeclass
-}

-- _ = AGraph
