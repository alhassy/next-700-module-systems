module Testing where
open import Testing_Generated

{-700
PackageFormer Magma (v : Variation) : Set where
  field
    _⨾_ : Magma v → Magma v → Magma v
    -- Id  : Magma v
    assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

Magma-typeclass = Magma typeclass
MagmaT = Magma typeclass
MagmaR = Magma record
MagmaD = Magma data
-}

_ = MagmaD
_ = MagmaR
_ = MagmaT
_ = Magma-typeclass

-- TODO: Support /multiple/ PackageFormer𝒮!
{-

PackageFormer Graph (v : Variation) : Set₁ where
  field
    Vertex : Set
    _⟶_ : Vertex → Vertex → Set

AGraph = Graph typeclass

-}
