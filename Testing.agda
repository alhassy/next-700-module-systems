-- (parse-700-comments)
-- instantiations-remaining
-- (setq package-formers nil)

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
MagmaT = Magma typeclass
MagmaR = Magma record
MagmaD = Magma data
-}

_ = Magma-typeclass
_ = MagmaT
_ = MagmaR
_ = MagmaD

{-700

PackageFormer Graph (v : Variation) : Set (ℓ.suc ℓ.zero) where
  field
    Vertex : Set
    _⟶_ : Vertex → Vertex → Set

AGraph = Graph typeclass renaming (Carrier to Vertex)
-}

_ = AGraph

{-00

TypeWithHole₁ = AGraph yet-undefined-variation
TypeWithHole₂ = MyPF data
-}

-- _ = TypeWithHole₁
--
-- Causes internal error.
--
-- _ = TypeWithHole₂
