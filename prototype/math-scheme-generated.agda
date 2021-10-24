{- This file is generated ;; do not alter. -}

import Relation.Binary.PropositionalEquality as ≡; open ≡ using (_≡_)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_)
open import Data.Product
open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _↔_) -- just to get by.
open import Level as Level using (Level)
module math-scheme-generated where


{- Kind “PackageFormer” does not correspond  to a concrete Agda type.

PackageFormer EmptyPF : Set₁ where
 -}


{- Empty   = EmptyPF ⟴ record -}
record Empty : Set₁ where


{- Carrier                              = Empty extended-by′ "U : Set" -}
record Carrier : Set₁ where
    field U     : Set


{- CarrierS                             = Empty extended-by′ "S : Set" -}
record CarrierS : Set₁ where
    field S     : Set


{- MultiCarrier                         = Carrier union′ CarrierS -}
record MultiCarrier : Set₁ where
    field U     : Set
    field S     : Set


{- PointedCarrier                       = Carrier extended-by′ "e : U" -}
record PointedCarrier : Set₁ where
    field U     : Set
    field e     : U


{- Pointed2Carrier                      = Carrier extended-by′ "e2 : U" -}
record Pointed2Carrier : Set₁ where
    field U     : Set
    field e2        : U


{- DoublyPointed                        = PointedCarrier union′ Pointed2Carrier -}
record DoublyPointed : Set₁ where
    field U     : Set
    field e     : U
    field e2        : U


{- DoublyPointed𝟘𝟙                      = DoublyPointed renaming′ "e to 𝟘; e2 to 𝟙" -}
record DoublyPointed𝟘𝟙 : Set₁ where
    field U     : Set
    field 𝟘     : U
    field 𝟙     : U


{- UnaryOperation                       = Carrier extended-by′ "prime : U → U" -}
record UnaryOperation : Set₁ where
    field U     : Set
    field prime     : U → U


{- Magma                                = Carrier extended-by′ "_*_ : U → U → U" -}
record Magma : Set₁ where
    field U     : Set
    field _*_       : U → U → U


{- UnaryRelation                        = Carrier extended-by′ "R : U → Set" -}
record UnaryRelation : Set₁ where
    field U     : Set
    field R     : U → Set


{- BinaryRelation                       = Carrier extended-by′ "R : U → U → Set" -}
record BinaryRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set


{- PointedUnarySystem                   = UnaryOperation union′ PointedCarrier -}
record PointedUnarySystem : Set₁ where
    field U     : Set
    field prime     : U → U
    field e     : U


{- FixedPoint                           = PointedUnarySystem extended-by′ "fixes_prime_e : prime e ≡ e" -}
record FixedPoint : Set₁ where
    field U     : Set
    field prime     : U → U
    field e     : U
    field fixes_prime_e     : prime e ≡ e


{- InvolutiveMagmaSig                   = UnaryOperation union′ Magma -}
record InvolutiveMagmaSig : Set₁ where
    field U     : Set
    field prime     : U → U
    field _*_       : U → U → U


{- InvolutivePointedMagmaSig            = PointedUnarySystem union′ Magma -}
record InvolutivePointedMagmaSig : Set₁ where
    field U     : Set
    field prime     : U → U
    field e     : U
    field _*_       : U → U → U


{- Involution                           = UnaryOperation extended-by′ "prime-involutive : ∀ (x : U) → prime (prime x) ≡ x" -}
record Involution : Set₁ where
    field U     : Set
    field prime     : U → U
    field prime-involutive      : ∀ (x : U) → prime (prime x) ≡ x


{- UnaryDistributes                     = InvolutiveMagmaSig extended-by′ "prime-*-distribute : ∀ (x y : U) → prime (x * y) ≡ (prime x * prime y)" -}
record UnaryDistributes : Set₁ where
    field U     : Set
    field prime     : U → U
    field _*_       : U → U → U
    field prime-*-distribute        : ∀ (x y : U) → prime (x * y) ≡ (prime x * prime y)


{- UnaryAntiDistribution                = InvolutiveMagmaSig extended-by′ "prime-*-antidistribute : ∀ (x y : U) → prime(x * y) ≡ (prime y * prime x)" -}
record UnaryAntiDistribution : Set₁ where
    field U     : Set
    field prime     : U → U
    field _*_       : U → U → U
    field prime-*-antidistribute        : ∀ (x y : U) → prime(x * y) ≡ (prime y * prime x)


{- AdditiveUnaryAntiDistribution        = UnaryAntiDistribution renaming′ "_*_ to _+_" -}
record AdditiveUnaryAntiDistribution : Set₁ where
    field U     : Set
    field prime     : U → U
    field _+_       : U → U → U
    field prime-+-antidistribute        : ∀ (x y : U) → prime(x + y) ≡ (prime y + prime x)


{- IdempotentUnary                      = UnaryOperation extended-by′ "prime-idempotent : ∀ (f : U) → prime (prime f) ≡ prime f" -}
record IdempotentUnary : Set₁ where
    field U     : Set
    field prime     : U → U
    field prime-idempotent      : ∀ (f : U) → prime (prime f) ≡ prime f


{- InvolutiveMagma                      = Involution union′ UnaryAntiDistribution ⟴ :remark "over UnaryOperation" -}
record InvolutiveMagma : Set₁ where
    field U     : Set
    field prime     : U → U
    field prime-involutive      : ∀ (x : U) → prime (prime x) ≡ x
    field _*_       : U → U → U
    field prime-*-antidistribute        : ∀ (x y : U) → prime(x * y) ≡ (prime y * prime x)


{- IrreflexiveRelation                  = BinaryRelation extended-by′ "R-irreflexive : ∀ (x : U)  →  ¬ (R x x)" -}
record IrreflexiveRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-irreflexive     : ∀ (x : U) → ¬ (R x x)


{- ReflexiveRelation                    = BinaryRelation extended-by′ "R-reflexive : ∀ (x : U)  →  R x x" -}
record ReflexiveRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-reflexive       : ∀ (x : U) → R x x


{- TransitiveRelation                   = BinaryRelation extended-by′ "R-transitive : ∀ (x y z : U) → R x y → R y z → R x z" -}
record TransitiveRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-transitive      : ∀ (x y z : U) → R x y → R y z → R x z


{- SymmetricRelation                    = BinaryRelation extended-by′ "R-symmetric : ∀ (x y : U) →  R x y →  R y x" -}
record SymmetricRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-symmetric       : ∀ (x y : U) → R x y → R y x


{- AntisymmetricRelation                = BinaryRelation extended-by′ "R-antisymmetric : ∀ (x y : U) → R y x → R x y → x ≡ y" -}
record AntisymmetricRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-antisymmetric       : ∀ (x y : U) → R y x → R x y → x ≡ y


{- OrderRelation                        = BinaryRelation renaming′ "R to _≤_" -}
record OrderRelation : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set


{- ReflexiveOrderRelation               = ReflexiveRelation renaming′ "R to _≤_" -}
record ReflexiveOrderRelation : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x


{- TransitiveOrderRelation              = TransitiveRelation renaming′ "R to _≤_" -}
record TransitiveOrderRelation : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z


{- SymmetricOrderRelation               = SymmetricRelation renaming′ "R to _≤_" -}
record SymmetricOrderRelation : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-symmetric       : ∀ (x y : U) → _≤_ x y → _≤_ y x


{- AntisymmetricOrderRelation           = AntisymmetricRelation renaming′ "R to _≤_" -}
record AntisymmetricOrderRelation : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- Preorder                             = ReflexiveOrderRelation union′ TransitiveOrderRelation ⟴ :remark "over OrderRelation" -}
record Preorder : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z


{- StrictPartialOrder                   = IrreflexiveRelation union′ TransitiveRelation ⟴ :remark "over BinaryRelation" -}
record StrictPartialOrder : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-irreflexive     : ∀ (x : U) → ¬ (R x x)
    field R-transitive      : ∀ (x y z : U) → R x y → R y z → R x z


{- EquivalenceRelation                  = ReflexiveRelation union′ TransitiveRelation ⟴ union′ SymmetricRelation :adjoin-retract₁ nil ⟴ :remark "over BinaryRelation" -}
record EquivalenceRelation : Set₁ where
    field U     : Set
    field R     : U → U → Set
    field R-reflexive       : ∀ (x : U) → R x x
    field R-transitive      : ∀ (x y z : U) → R x y → R y z → R x z
    field R-symmetric       : ∀ (x y : U) → R x y → R y x


{- PartialOrder                         = Preorder union′ AntisymmetricOrderRelation  ⟴ :remark "over OrderRelation" -}
record PartialOrder : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- PartiallyOrderedMagmaSig             = Magma union′ OrderRelation ⟴ :remark "over Carrier" -}
record PartiallyOrderedMagmaSig : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set


{- OrderPreservingMagma                 = PartiallyOrderedMagmaSig extended-by′ "*-≤-orderPreserving : ∀ (x y u v : U) → x ≤ y → (u * (x * v)) ≤ (u * (y * v))" -}
record OrderPreservingMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y u v : U) → x ≤ y → (u * (x * v)) ≤ (u * (y * v))


{- PartiallyOrderedMagma                = OrderPreservingMagma union′ PartialOrder ⟴ :remark "over OrderRelation" -}
record PartiallyOrderedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- TotalRelation                        = OrderRelation extended-by′ "≤-total : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)" -}
record TotalRelation : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- TotalPreorder                        = Preorder union′ TotalRelation ⟴ :remark "over OrderRelation" -}
record TotalPreorder : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- TotalOrder                           = TotalPreorder union′ AntisymmetricOrderRelation ⟴ :remark "over Preorder" -}
record TotalOrder : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- OrderedMagma                         = PartiallyOrderedMagma union′ TotalRelation ⟴ :remark "over OrderRelation" -}
record OrderedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- LeftCanonicalOrder                   = PartiallyOrderedMagmaSig extended-by′ "≤-*-leftCanonicalOrder : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)" -}
record LeftCanonicalOrder : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)


{- RightCanonicalOrder                  = PartiallyOrderedMagmaSig extended-by′ "≤-*-rightCanonicalOrder : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)" -}
record RightCanonicalOrder : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)


{- LeftCanonicallyOrderedMagma          = OrderedMagma union′ LeftCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record LeftCanonicallyOrderedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)


{- RightCanonicallyOrderedMagma         = OrderedMagma union′ RightCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record RightCanonicallyOrderedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)


{- CanonicallyOrderedMagma              = LeftCanonicallyOrderedMagma union′ RightCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record CanonicallyOrderedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)


{- Chain                                = TotalOrder -}
record Chain : Set₁ where
    field U     : Set
    field _≤_       : U → U → Set
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- AdditiveMagma                        = Magma renaming′ "_*_ to _+_" -}
record AdditiveMagma : Set₁ where
    field U     : Set
    field _+_       : U → U → U


{- LeftDivisionMagma                    = Magma renaming′ "_*_ to _╲_" -}
record LeftDivisionMagma : Set₁ where
    field U     : Set
    field _╲_       : U → U → U


{- RightDivisionMagma                   = Magma renaming′ "_*_ to _╱_" -}
record RightDivisionMagma : Set₁ where
    field U     : Set
    field _╱_       : U → U → U


{- LeftOperation                        = MultiCarrier extended-by′ "_⟫_ : U → S → S" -}
record LeftOperation : Set₁ where
    field U     : Set
    field S     : Set
    field _⟫_       : U → S → S


{- RightOperation                       = MultiCarrier extended-by′ "_⟪_ : S → U → S" -}
record RightOperation : Set₁ where
    field U     : Set
    field S     : Set
    field _⟪_       : S → U → S


{- IdempotentMagma                      = Magma extended-by′ "*-idempotent : ∀ (x : U) → (x * x) ≡ x" -}
record IdempotentMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-idempotent      : ∀ (x : U) → (x * x) ≡ x


{- IdempotentAdditiveMagma              = IdempotentMagma renaming′ "_*_ to _+_" -}
record IdempotentAdditiveMagma : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-idempotent      : ∀ (x : U) → (x + x) ≡ x


{- SelectiveMagma                       = Magma extended-by′ "*-selective : ∀ (x y : U) → (x * y ≡ x) ⊎ (x * y ≡ y)" -}
record SelectiveMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-selective       : ∀ (x y : U) → (x * y ≡ x) ⊎ (x * y ≡ y)


{- SelectiveAdditiveMagma               = SelectiveMagma renaming′ "_*_ to _+_" -}
record SelectiveAdditiveMagma : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-selective       : ∀ (x y : U) → (x + y ≡ x) ⊎ (x + y ≡ y)


{- PointedMagma                         = Magma union′ PointedCarrier ⟴ :remark "over Carrier" -}
record PointedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U


{- Pointed𝟘Magma                        = PointedMagma renaming′ "e to 𝟘" -}
record Pointed𝟘Magma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟘     : U


{- AdditivePointed1Magma                = PointedMagma renaming′ "_*_ to _+_; e to 𝟙" -}
record AdditivePointed1Magma : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟙     : U


{- LeftPointAction                      = PointedMagma extended-by "pointactLeft  :  U → U; pointactLeft x = e * x" -}
record LeftPointAction : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    pointactLeft        : U → U ;   pointactLeft x = e * x
    toPointedMagma      : let View X = X in View PointedMagma ; toPointedMagma = record {U = U;_*_ = _*_;e = e}


{- RightPointAction                     = PointedMagma extended-by "pointactRight  :  U → U; pointactRight x = x * e" -}
record RightPointAction : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    pointactRight       : U → U ;   pointactRight x = x * e
    toPointedMagma      : let View X = X in View PointedMagma ; toPointedMagma = record {U = U;_*_ = _*_;e = e}


{- CommutativeMagma                     = Magma extended-by′ "*-commutative  :  ∀ (x y : U) →  (x * y) ≡ (y * x)" -}
record CommutativeMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- CommutativeAdditiveMagma             = CommutativeMagma renaming′ "_*_ to _+_" -}
record CommutativeAdditiveMagma : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)


{- PointedCommutativeMagma              = PointedMagma union′ CommutativeMagma ⟴ :remark "over Magma" -}
record PointedCommutativeMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- AntiAbsorbent                        = Magma extended-by′ "*-anti-self-absorbent  : ∀ (x y : U) → (x * (x * y)) ≡ y" -}
record AntiAbsorbent : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-anti-self-absorbent     : ∀ (x y : U) → (x * (x * y)) ≡ y


{- SteinerMagma                         = CommutativeMagma union′ AntiAbsorbent ⟴ :remark "over Magma" -}
record SteinerMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field *-anti-self-absorbent     : ∀ (x y : U) → (x * (x * y)) ≡ y


{- Squag                                = SteinerMagma union′ IdempotentMagma ⟴ :remark "over Magma" -}
record Squag : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field *-anti-self-absorbent     : ∀ (x y : U) → (x * (x * y)) ≡ y
    field *-idempotent      : ∀ (x : U) → (x * x) ≡ x


{- PointedSteinerMagma                  = PointedMagma union′ SteinerMagma ⟴ :remark "over Magma" -}
record PointedSteinerMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field *-anti-self-absorbent     : ∀ (x y : U) → (x * (x * y)) ≡ y


{- UnipotentPointedMagma                = PointedMagma extended-by′ "unipotent  : ∀ (x : U) →  (x * x) ≡ e" -}
record UnipotentPointedMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field unipotent     : ∀ (x : U) → (x * x) ≡ e


{- Sloop                                = PointedSteinerMagma union′ UnipotentPointedMagma ⟴ :remark "over PointedMagma" -}
record Sloop : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field *-anti-self-absorbent     : ∀ (x y : U) → (x * (x * y)) ≡ y
    field unipotent     : ∀ (x : U) → (x * x) ≡ e


{- LeftDistributiveMagma                = Magma extended-by′ "*-leftDistributive : ∀ (x y z : U) → (x * (y * z)) ≡ ((x * y) * (x * z))" -}
record LeftDistributiveMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-leftDistributive        : ∀ (x y z : U) → (x * (y * z)) ≡ ((x * y) * (x * z))


{- RightDistributiveMagma               = Magma extended-by′ "*-rightDistributive : ∀ (x y z : U) → ((y * z) * x) ≡ ((y * x) * (z * x))" -}
record RightDistributiveMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-rightDistributive       : ∀ (x y z : U) → ((y * z) * x) ≡ ((y * x) * (z * x))


{- LeftCancellativeMagma                = Magma extended-by′ "*-leftCancellative  :  ∀ (x y z : U) → z * x ≡ z * y → x ≡ y" -}
record LeftCancellativeMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y


{- RightCancellativeMagma               = Magma extended-by′ "*-rightCancellative  : ∀ (x y z : U) →  x * z ≡ y * z → x ≡ y" -}
record RightCancellativeMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- CancellativeMagma                    = LeftCancellativeMagma union′ RightCancellativeMagma ⟴ :remark "over Magma" -}
record CancellativeMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- LeftUnital                           = PointedMagma extended-by′ "*-leftIdentity : ∀ (x : U) →  e * x ≡ x" -}
record LeftUnital : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x


{- RightUnital                          = PointedMagma extended-by′ "*-rightIdentity : ∀ (x : U) →  x * e ≡ x" -}
record RightUnital : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x


{- Unital                               = LeftUnital union′ RightUnital ⟴ :remark "over PointedMagma" -}
record Unital : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x


{- LeftBiMagma                          = LeftDivisionMagma union′ Magma :adjoin-retract₂ "toMagma*" ⟴ :remark "over Carrier" -}
record LeftBiMagma : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U


{- RightBiMagma                         = LeftBiMagma renaming′ "_╲_ to _╱_" -}
record RightBiMagma : Set₁ where
    field U     : Set
    field _╱_       : U → U → U
    field _*_       : U → U → U


{- LeftCancellative                     = LeftBiMagma extended-by′ "*-╲-leftCancel : ∀ (x y : U) →  x * (x ╲ y) ≡ y" -}
record LeftCancellative : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y


{- LeftCancellativeOp                   = LeftBiMagma extended-by′ "╲-╲-leftCancel : ∀ (x y : U) →  x ╲ (x * y) ≡ y" -}
record LeftCancellativeOp : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y


{- LeftQuasiGroup                       = LeftCancellative union′ LeftCancellativeOp ⟴ :remark "over LeftBiMagma" -}
record LeftQuasiGroup : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y


{- RightCancellative                    = RightBiMagma extended-by′ "╱-*-rightCancel : ∀ (x y : U) →  (y ╱ x) * x ≡ y" -}
record RightCancellative : Set₁ where
    field U     : Set
    field _╱_       : U → U → U
    field _*_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y


{- RightCancellativeOp                  = RightBiMagma extended-by′ "*-╱-rightCancel : ∀ (x y : U) → (y * x) ╱ x ≡ y" -}
record RightCancellativeOp : Set₁ where
    field U     : Set
    field _╱_       : U → U → U
    field _*_       : U → U → U
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y


{- RightQuasiGroup                      = RightCancellative union′ RightCancellativeOp ⟴ :remark "over RightBiMagma" -}
record RightQuasiGroup : Set₁ where
    field U     : Set
    field _╱_       : U → U → U
    field _*_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y


{- QuasiGroup                           = LeftQuasiGroup union′ RightQuasiGroup -}
record QuasiGroup : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y
    field _╱_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y


{- MedialMagma                          = Magma extended-by′ "mediate : ∀ (w x y z : U) →  (x * y) * (z * w) ≡ (x * z) * (y * w)" -}
record MedialMagma : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field mediate       : ∀ (w x y z : U) → (x * y) * (z * w) ≡ (x * z) * (y * w)


{- MedialQuasiGroup                     = QuasiGroup union′ MedialMagma ⟴ :remark "over Magma" -}
record MedialQuasiGroup : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y
    field _╱_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y
    field mediate       : ∀ (w x y z : U) → (x * y) * (z * w) ≡ (x * z) * (y * w)


{- MoufangLaw                           = Magma extended-by′ "*-moufangLaw : ∀ (e x y z : U)  →  (y * e ≡ y)  →  ((x * y) * z) * x  ≡  x * (y * ((e * z) * x))" -}
record MoufangLaw : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-moufangLaw      : ∀ (e x y z : U) → (y * e ≡ y) → ((x * y) * z) * x ≡ x * (y * ((e * z) * x))


{- MoufangQuasigroup                    = QuasiGroup union′ MoufangLaw ⟴ :remark "over Magma" -}
record MoufangQuasigroup : Set₁ where
    field U     : Set
    field _╲_       : U → U → U
    field _*_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y
    field _╱_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y
    field *-moufangLaw      : ∀ (e x y z : U) → (y * e ≡ y) → ((x * y) * z) * x ≡ x * (y * ((e * z) * x))


{- LeftLoop                             = RightUnital union′ LeftQuasiGroup ⟴ :remark "over Magma" -}
record LeftLoop : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field _╲_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y


{- Loop                                 = Unital union′ QuasiGroup ⟴ :remark "over Magma" -}
record Loop : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field _╲_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y
    field _╱_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y


{- MoufangAlgebra                       = Magma extended-by′ "*-MoufangIdentity : ∀ (x y z : U) → (z * x) * (y * z) ≡ (z * (x * y)) * z" -}
record MoufangAlgebra : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-MoufangIdentity     : ∀ (x y z : U) → (z * x) * (y * z) ≡ (z * (x * y)) * z


{- MoufangLoop                          = Loop union′ MoufangAlgebra ⟴ :remark "over Magma" -}
record MoufangLoop : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field _╲_       : U → U → U
    field *-╲-leftCancel        : ∀ (x y : U) → x * (x ╲ y) ≡ y
    field ╲-╲-leftCancel        : ∀ (x y : U) → x ╲ (x * y) ≡ y
    field _╱_       : U → U → U
    field ╱-*-rightCancel       : ∀ (x y : U) → (y ╱ x) * x ≡ y
    field *-╱-rightCancel       : ∀ (x y : U) → (y * x) ╱ x ≡ y
    field *-MoufangIdentity     : ∀ (x y z : U) → (z * x) * (y * z) ≡ (z * (x * y)) * z


{- LeftShelfSig                         = Magma renaming′ "_*_ to _|>_" -}
record LeftShelfSig : Set₁ where
    field U     : Set
    field _|>_      : U → U → U


{- LeftShelf                            = LeftDistributiveMagma renaming′ "_*_ to _|>_" -}
record LeftShelf : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field |>-leftDistributive       : ∀ (x y z : U) → (x |> (y |> z)) ≡ ((x |> y) |> (x |> z))


{- RightShelfSig                        = Magma renaming′ "_*_ to _<|_ " -}
record RightShelfSig : Set₁ where
    field U     : Set
    field _<|_      : U → U → U


{- RightShelf                           = RightDistributiveMagma renaming′ "_*_ to _<|_ " -}
record RightShelf : Set₁ where
    field U     : Set
    field _<|_      : U → U → U
    field <|-rightDistributive      : ∀ (x y z : U) → ((y <| z) <| x) ≡ ((y <| x) <| (z <| x))


{- RackSig                              = LeftShelfSig union′ RightShelfSig ⟴ :remark "over Carrier" -}
record RackSig : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field _<|_      : U → U → U


{- Shelf                                = LeftShelf union′ RightShelf ⟴ :remark "over RackSig" -}
record Shelf : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field |>-leftDistributive       : ∀ (x y z : U) → (x |> (y |> z)) ≡ ((x |> y) |> (x |> z))
    field _<|_      : U → U → U
    field <|-rightDistributive      : ∀ (x y z : U) → ((y <| z) <| x) ≡ ((y <| x) <| (z <| x))


{- LeftBinaryInverse                    = RackSig extended-by′ "|>-<|-absorption : ∀ (x y : U) →  (x |> y) <| x ≡ y" -}
record LeftBinaryInverse : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field _<|_      : U → U → U
    field |>-<|-absorption      : ∀ (x y : U) → (x |> y) <| x ≡ y


{- RightBinaryInverse                   = RackSig extended-by′ "|>-<|-co-absorption : ∀ (x y : U) →  x |> (y <| x) ≡ y" -}
record RightBinaryInverse : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field _<|_      : U → U → U
    field |>-<|-co-absorption       : ∀ (x y : U) → x |> (y <| x) ≡ y


{- Rack                                 = RightShelf union′ LeftShelf ⟴ union′ LeftBinaryInverse union′ ⟴ union′ RightBinaryInverse ⟴ :remark "over RackSig" -}
record Rack : Set₁ where
    field U     : Set
    field _<|_      : U → U → U
    field <|-rightDistributive      : ∀ (x y z : U) → ((y <| z) <| x) ≡ ((y <| x) <| (z <| x))
    field _|>_      : U → U → U
    field |>-leftDistributive       : ∀ (x y z : U) → (x |> (y |> z)) ≡ ((x |> y) |> (x |> z))
    field |>-<|-absorption      : ∀ (x y : U) → (x |> y) <| x ≡ y
    field |>-<|-co-absorption       : ∀ (x y : U) → x |> (y <| x) ≡ y


{- LeftIdempotence                      = IdempotentMagma renaming′ "_*_ to _|>_" -}
record LeftIdempotence : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field |>-idempotent     : ∀ (x : U) → (x |> x) ≡ x


{- RightIdempotence                     = IdempotentMagma renaming′ "_*_ to _<|_" -}
record RightIdempotence : Set₁ where
    field U     : Set
    field _<|_      : U → U → U
    field <|-idempotent     : ∀ (x : U) → (x <| x) ≡ x


{- LeftSpindle                          = LeftShelf union′ LeftIdempotence ⟴ :remark "over LeftShelfSig" -}
record LeftSpindle : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field |>-leftDistributive       : ∀ (x y z : U) → (x |> (y |> z)) ≡ ((x |> y) |> (x |> z))
    field |>-idempotent     : ∀ (x : U) → (x |> x) ≡ x


{- RightSpindle                         = RightShelf union′ RightIdempotence ⟴ :remark "over RightShelfSig" -}
record RightSpindle : Set₁ where
    field U     : Set
    field _<|_      : U → U → U
    field <|-rightDistributive      : ∀ (x y z : U) → ((y <| z) <| x) ≡ ((y <| x) <| (z <| x))
    field <|-idempotent     : ∀ (x : U) → (x <| x) ≡ x


{- Quandle                              = Rack union′ LeftSpindle ⟴ union′ RightSpindle ⟴ :adjoin-retract₁ nil ⟴ :remark "over Shelf" -}
record Quandle : Set₁ where
    field U     : Set
    field _<|_      : U → U → U
    field <|-rightDistributive      : ∀ (x y z : U) → ((y <| z) <| x) ≡ ((y <| x) <| (z <| x))
    field _|>_      : U → U → U
    field |>-leftDistributive       : ∀ (x y z : U) → (x |> (y |> z)) ≡ ((x |> y) |> (x |> z))
    field |>-<|-absorption      : ∀ (x y : U) → (x |> y) <| x ≡ y
    field |>-<|-co-absorption       : ∀ (x y : U) → x |> (y <| x) ≡ y
    field |>-idempotent     : ∀ (x : U) → (x |> x) ≡ x
    field <|-idempotent     : ∀ (x : U) → (x <| x) ≡ x


{- RightSelfInverse                     = LeftShelfSig extended-by′ "rightSelfInverse_|> : ∀ (x y : U) →  (x |> y) |> y ≡ x" -}
record RightSelfInverse : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field rightSelfInverse_|>       : ∀ (x y : U) → (x |> y) |> y ≡ x


{- Kei                                  = LeftSpindle union′ RightSelfInverse ⟴ :remark "over LeftShelfSig" -}
record Kei : Set₁ where
    field U     : Set
    field _|>_      : U → U → U
    field |>-leftDistributive       : ∀ (x y z : U) → (x |> (y |> z)) ≡ ((x |> y) |> (x |> z))
    field |>-idempotent     : ∀ (x : U) → (x |> x) ≡ x
    field rightSelfInverse_|>       : ∀ (x y : U) → (x |> y) |> y ≡ x


{- Semigroup                            = Magma extended-by′ "*-associative : ∀ (x y z : U) →  (x * y) * z  ≡  x * (y * z)" -}
record Semigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- AdditiveSemigroup                    = Semigroup renaming′ "_*_ to _+_" -}
record AdditiveSemigroup : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)


{- CommutativeSemigroup                 = Semigroup union′ CommutativeMagma ⟴ :remark "over Magma" -}
record CommutativeSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- AdditiveCommutativeSemigroup         = CommutativeSemigroup renaming′ "_*_ to _+_" -}
record AdditiveCommutativeSemigroup : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)


{- LeftCancellativeSemigroup            = Semigroup union′ LeftCancellativeMagma ⟴ :remark "over Magma" -}
record LeftCancellativeSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y


{- RightCancellativeSemigroup           = Semigroup union′ RightCancellativeMagma ⟴ :remark "over Magma" -}
record RightCancellativeSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- CancellativeSemigroup                = Semigroup union′ CancellativeMagma ⟴ :remark "over Magma" -}
record CancellativeSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- CancellativeCommutativeSemigroup     = CommutativeSemigroup union′ CancellativeSemigroup ⟴ :remark "over Semigroup" -}
record CancellativeCommutativeSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- InvolutiveSemigroup                  = Semigroup union′ InvolutiveMagma ⟴ :remark "over PointedMagma" -}
record InvolutiveSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field prime     : U → U
    field prime-involutive      : ∀ (x : U) → prime (prime x) ≡ x
    field prime-*-antidistribute        : ∀ (x y : U) → prime(x * y) ≡ (prime y * prime x)


{- PartiallyOrderedSemigroup            = PartiallyOrderedMagma union′ Semigroup ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record PartiallyOrderedSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- OrderedSemigroup                     = PartiallyOrderedSemigroup union′ TotalRelation ⟴ :remark "over OrderRelation" -}
record OrderedSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- CommutativePartiallyOrderedSemigroup = CommutativeSemigroup union′ PartiallyOrderedSemigroup ⟴ :remark "over Semigroup" -}
record CommutativePartiallyOrderedSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- CommutativeOrderedSemigroup          = CommutativeSemigroup union′ OrderedSemigroup ⟴ :remark "over Semigroup" -}
record CommutativeOrderedSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- Band                                 = Semigroup union′ IdempotentMagma ⟴ :remark "over Magma" -}
record Band : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-idempotent      : ∀ (x : U) → (x * x) ≡ x


{- CommutativeBand                      = Band union′ CommutativeMagma ⟴ :remark "over Magma" -}
record CommutativeBand : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-idempotent      : ∀ (x : U) → (x * x) ≡ x
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- MiddleAbsorption                     = Magma extended-by′ "*-middleAbsorb : ∀ (x y z : U) →  x * (y * z)  ≡  x * z" -}
record MiddleAbsorption : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-middleAbsorb        : ∀ (x y z : U) → x * (y * z) ≡ x * z


{- MiddleCommute                        = Magma extended-by′ "*-middleCommute : ∀ (x y z : U) → (x * y) * (z * x)  ≡  (x * z) * (y * x)" -}
record MiddleCommute : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-middleCommute       : ∀ (x y z : U) → (x * y) * (z * x) ≡ (x * z) * (y * x)


{- RectangularBand                      = Band union′ MiddleAbsorption ⟴ :remark "over Magma" -}
record RectangularBand : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-idempotent      : ∀ (x : U) → (x * x) ≡ x
    field *-middleAbsorb        : ∀ (x y z : U) → x * (y * z) ≡ x * z


{- NormalBand                           = Band union′ MiddleCommute ⟴ :remark "over Magma" -}
record NormalBand : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-idempotent      : ∀ (x : U) → (x * x) ≡ x
    field *-middleCommute       : ∀ (x y z : U) → (x * y) * (z * x) ≡ (x * z) * (y * x)


{- RightMonoid                          = RightUnital union′ Semigroup ⟴ :remark "over Magma" -}
record RightMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- LeftMonoid                           = LeftUnital union′ Semigroup ⟴ :remark "over Magma" -}
record LeftMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- Monoid                               = Unital union′ Semigroup ⟴ :remark "over Magma" -}
record Monoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- AdditiveMonoid                       = Monoid renaming′ "_*_ to _+_; e to 𝟘" -}
record AdditiveMonoid : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)


{- DoubleMonoid                         = Monoid union′ AdditiveMonoid ⟴ :remark "over Carrier" -}
record DoubleMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)


{- Monoid1                              = Monoid renaming′ "e to 𝟙" -}
record Monoid1 : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- CommutativeMonoid                    = Monoid union′ CommutativeSemigroup ⟴ :remark "over Semigroup" -}
record CommutativeMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- SelectiveMonoid                      = Monoid union′ SelectiveMagma ⟴ :remark "over Magma" -}
record SelectiveMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-selective       : ∀ (x y : U) → (x * y ≡ x) ⊎ (x * y ≡ y)


{- CancellativeMonoid                   = Monoid union′ CancellativeMagma ⟴ :remark "over Magma" -}
record CancellativeMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- CancellativeCommutativeMonoid        = CancellativeMonoid union′ CommutativeMonoid ⟴ :remark "over Monoid" -}
record CancellativeCommutativeMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- LeftZero                             = PointedMagma extended-by′ "*-leftZero : ∀ (x : U) → e * x ≡ e" -}
record LeftZero : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftZero        : ∀ (x : U) → e * x ≡ e


{- RightZero                            = PointedMagma extended-by′ "*-rightZero : ∀ (x : U) → x * e ≡ e" -}
record RightZero : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-rightZero       : ∀ (x : U) → x * e ≡ e


{- Zero                                 = LeftZero union′ RightZero ⟴ :remark "over PointedMagma" -}
record Zero : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftZero        : ∀ (x : U) → e * x ≡ e
    field *-rightZero       : ∀ (x : U) → x * e ≡ e


{- Left0                                = LeftZero renaming′ "e to 𝟘" -}
record Left0 : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟘     : U
    field *-leftZero        : ∀ (x : U) → 𝟘 * x ≡ 𝟘


{- Right0                               = RightZero renaming′ "e to 𝟘" -}
record Right0 : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟘     : U
    field *-rightZero       : ∀ (x : U) → x * 𝟘 ≡ 𝟘


{- ComplementSig                        = UnaryOperation renaming′ "prime to compl" -}
record ComplementSig : Set₁ where
    field U     : Set
    field compl     : U → U


{- CommutativeMonoid1                   = CommutativeMonoid renaming′ "e to 𝟙" -}
record CommutativeMonoid1 : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- AdditiveCommutativeMonoid            = CommutativeMonoid renaming′ "_*_ to _+_; e to 𝟘" -}
record AdditiveCommutativeMonoid : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)


{- PartiallyOrderedMonoid               = PartiallyOrderedMagma union′ Monoid ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record PartiallyOrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- OrderedMonoid                        = PartiallyOrderedMonoid union′ TotalRelation ⟴ :remark "over OrderRelation" -}
record OrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- CommutativePartiallyOrderedMonoid    = CommutativeMonoid union′ PartiallyOrderedMonoid ⟴ :remark "over Monoid" -}
record CommutativePartiallyOrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y


{- CommutativeOrderedMonoid             = CommutativeMonoid union′ OrderedMonoid ⟴ :remark "over Monoid" -}
record CommutativeOrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- LeftCanonicallyPreorderedMonoid      = Monoid union′ LeftCanonicalOrder ⟴ union′ Preorder ⟴ :adjoin-retract₁ nil ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record LeftCanonicallyPreorderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field _≤_       : U → U → Set
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z


{- RightCanonicallyPreorderedMonoid     = Monoid union′ RightCanonicalOrder ⟴ union′ Preorder ⟴ :adjoin-retract₁ nil ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record RightCanonicallyPreorderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field _≤_       : U → U → Set
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z


{- CanonicallyPreorderedMonoid          = LeftCanonicallyPreorderedMonoid union′ RightCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record CanonicallyPreorderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field _≤_       : U → U → Set
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)


{- LeftCanonicallyOrderedMonoid         = PartiallyOrderedMonoid union′ LeftCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record LeftCanonicallyOrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)


{- RightCanonicallyOrderedMonoid        = PartiallyOrderedMonoid union′ LeftCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record RightCanonicallyOrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)


{- CanonicallyOrderedMonoid             = LeftCanonicallyOrderedMonoid union′ RightCanonicalOrder ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record CanonicallyOrderedMonoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)


{- AdditiveCanonicallyOrderedMonoid     = CanonicallyOrderedMonoid renaming′ "_*_ to _+_; e to 𝟘" -}
record AdditiveCanonicallyOrderedMonoid : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)


{- HemiGroup                            = CanonicallyOrderedMonoid union′ CancellativeMagma ⟴ :remark "over Magma" -}
record HemiGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field ≤-*-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a * c)
    field ≤-*-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c * a)
    field *-leftCancellative        : ∀ (x y z : U) → z * x ≡ z * y → x ≡ y
    field *-rightCancellative       : ∀ (x y z : U) → x * z ≡ y * z → x ≡ y


{- AdditiveHemiGroup                    = HemiGroup renaming′ "_*_ to _+_; e to 𝟘" -}
record AdditiveHemiGroup : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)
    field +-leftCancellative        : ∀ (x y z : U) → z + x ≡ z + y → x ≡ y
    field +-rightCancellative       : ∀ (x y z : U) → x + z ≡ y + z → x ≡ y


{- BooleanGroup                         = Monoid union′ UnipotentPointedMagma ⟴ :remark "over PointedMagma" -}
record BooleanGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field unipotent     : ∀ (x : U) → (x * x) ≡ e


{- InverseSig                           = InvolutivePointedMagmaSig renaming′ "prime to inv" -}
record InverseSig : Set₁ where
    field U     : Set
    field inv       : U → U
    field e     : U
    field _*_       : U → U → U


{- LeftInverse                          = InverseSig extended-by′ "*-leftInverse : ∀ (x : U) →  x * (inv x) ≡ e" -}
record LeftInverse : Set₁ where
    field U     : Set
    field inv       : U → U
    field e     : U
    field _*_       : U → U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e


{- RightInverse                         = InverseSig extended-by′ "*-rightInverse : ∀ (x : U) → (inv x) * x ≡ e" -}
record RightInverse : Set₁ where
    field U     : Set
    field inv       : U → U
    field e     : U
    field _*_       : U → U → U
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e


{- Inverse                              = LeftInverse union′ RightInverse ⟴ :remark "over InverseSig" -}
record Inverse : Set₁ where
    field U     : Set
    field inv       : U → U
    field e     : U
    field _*_       : U → U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e


{- PseudoInverseSig                     = InvolutiveMagmaSig renaming′ "prime to inv" -}
record PseudoInverseSig : Set₁ where
    field U     : Set
    field inv       : U → U
    field _*_       : U → U → U


{- PseudoInverse                        = PseudoInverseSig extended-by′ "*-quasiLeftInverse : ∀ (x : U) →  x * ((inv x) * x) ≡  x" -}
record PseudoInverse : Set₁ where
    field U     : Set
    field inv       : U → U
    field _*_       : U → U → U
    field *-quasiLeftInverse        : ∀ (x : U) → x * ((inv x) * x) ≡ x


{- PseudoInvolution                     = PseudoInverseSig extended-by′ "*-quasiRightInverse : ∀ (x : U) → (inv x * x) * inv x ≡ inv x" -}
record PseudoInvolution : Set₁ where
    field U     : Set
    field inv       : U → U
    field _*_       : U → U → U
    field *-quasiRightInverse       : ∀ (x : U) → (inv x * x) * inv x ≡ inv x


{- RegularSemigroup                     = Semigroup union′ PseudoInverse ⟴ :remark "over Magma" -}
record RegularSemigroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-quasiLeftInverse        : ∀ (x : U) → x * ((inv x) * x) ≡ x


{- InverseSemigroup                     = PseudoInverse union′ PseudoInvolution ⟴ :remark "over PseudoInverseSig" -}
record InverseSemigroup : Set₁ where
    field U     : Set
    field inv       : U → U
    field _*_       : U → U → U
    field *-quasiLeftInverse        : ∀ (x : U) → x * ((inv x) * x) ≡ x
    field *-quasiRightInverse       : ∀ (x : U) → (inv x * x) * inv x ≡ inv x


{- Group                                = Monoid union′ Inverse ⟴ :remark "over InverseSig" -}
record Group : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e


{- Group1                               = Group renaming′ "e to 𝟙" -}
record Group1 : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ 𝟙
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ 𝟙


{- AdditiveGroup                        = Group renaming′ "_*_ to _+_; e to 𝟘; inv to neg" -}
record AdditiveGroup : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field neg       : U → U
    field +-leftInverse     : ∀ (x : U) → x + (neg x) ≡ 𝟘
    field +-rightInverse        : ∀ (x : U) → (neg x) + x ≡ 𝟘


{- AbelianGroup                         = Group1 union′ CommutativeMonoid1 ⟴ :remark "over Monoid1" -}
record AbelianGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ 𝟙
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ 𝟙
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- AbelianAdditiveGroup                 = AdditiveGroup union′ CommutativeAdditiveMagma ⟴ :remark "over AdditiveMagma" -}
record AbelianAdditiveGroup : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field neg       : U → U
    field +-leftInverse     : ∀ (x : U) → x + (neg x) ≡ 𝟘
    field +-rightInverse        : ∀ (x : U) → (neg x) + x ≡ 𝟘
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)


{- PartiallyOrderedGroup                = PartiallyOrderedMagma union′ Group ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record PartiallyOrderedGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e


{- OrderedGroup                         = PartiallyOrderedGroup union′ TotalRelation ⟴ :remark "over OrderRelation" -}
record OrderedGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- AbelianPartiallyOrderedGroup         = PartiallyOrderedMagma union′ AbelianGroup ⟴ :remark "over PartiallyOrderedMagmaSig" -}
record AbelianPartiallyOrderedGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ 𝟙
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ 𝟙
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)


{- AbelianOrderedGroup                  = AbelianPartiallyOrderedGroup union′ TotalRelation ⟴ :remark "over OrderRelation" -}
record AbelianOrderedGroup : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _≤_       : U → U → Set
    field *-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U * (x * v)) ≤ (U * (y * v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ 𝟙
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ 𝟙
    field *-commutative     : ∀ (x y : U) → (x * y) ≡ (y * x)
    field ≤-total       : ∀ (x y : U) → (x ≤ y) ⊎ (y ≤ x)


{- RingoidSig                           = Magma union′ AdditiveMagma :adjoin-retract₁ "*-isMagma" :adjoin-retract₂ "+-isMagma" ⟴ :remark "over Carrier" -}
record RingoidSig : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U


{- Pointed0Sig                          = PointedCarrier renaming′ "e to 𝟘" -}
record Pointed0Sig : Set₁ where
    field U     : Set
    field 𝟘     : U


{- Pointed1Sig                          = PointedCarrier renaming′ "e to 𝟙" -}
record Pointed1Sig : Set₁ where
    field U     : Set
    field 𝟙     : U


{- Ringoid0Sig                          = RingoidSig union′ Pointed0Sig ⟴ :remark "over Carrier" -}
record Ringoid0Sig : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field 𝟘     : U


{- Ringoid1Sig                          = RingoidSig union′ Pointed1Sig ⟴ :remark "over Carrier" -}
record Ringoid1Sig : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field 𝟙     : U


{- Ringoid01Sig                         = Ringoid0Sig union′ Ringoid1Sig ⟴ :remark "over RingoidSig" -}
record Ringoid01Sig : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field 𝟘     : U
    field 𝟙     : U


{- LeftRingoid                          = RingoidSig extended-by′ "*-+-leftDistributivity : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)" -}
record LeftRingoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)


{- RightRingoid                         = RingoidSig extended-by′ "*-+-rightDistributivity : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)" -}
record RightRingoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- Ringoid                              = LeftRingoid  union′ RightRingoid ⟴ :remark "over RingoidSig" -}
record Ringoid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- NonassociativeNondistributiveRing    = AbelianAdditiveGroup union′ Magma ⟴ :remark "over Carrier" -}
record NonassociativeNondistributiveRing : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field neg       : U → U
    field +-leftInverse     : ∀ (x : U) → x + (neg x) ≡ 𝟘
    field +-rightInverse        : ∀ (x : U) → (neg x) + x ≡ 𝟘
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _*_       : U → U → U


{- NonassociativeRing                   =  NonassociativeNondistributiveRing union′ Ringoid ⟴ :remark "over RingoidSig" -}
record NonassociativeRing : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field neg       : U → U
    field +-leftInverse     : ∀ (x : U) → x + (neg x) ≡ 𝟘
    field +-rightInverse        : ∀ (x : U) → (neg x) + x ≡ 𝟘
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _*_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- PrimeRingoidSig                      = RingoidSig  union′  UnaryOperation ⟴ :remark "over Carrier" -}
record PrimeRingoidSig : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field prime     : U → U


{- AnddeMorgan                          = PrimeRingoidSig extended-by′ "prime-*-+-deMorgan : ∀ (x y z : U) → prime (x * y) ≡ (prime x) + (prime y)" -}
record AnddeMorgan : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field prime     : U → U
    field prime-*-+-deMorgan        : ∀ (x y z : U) → prime (x * y) ≡ (prime x) + (prime y)


{- OrdeMorgan                           = PrimeRingoidSig extended-by′ "prime-+-*-deMorgan : ∀ (x y z : U) → prime (x + y) ≡ (prime x) * (prime y)" -}
record OrdeMorgan : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field prime     : U → U
    field prime-+-*-deMorgan        : ∀ (x y z : U) → prime (x + y) ≡ (prime x) * (prime y)


{- DualdeMorgan                         = OrdeMorgan union′ AnddeMorgan ⟴ :remark "over PrimeRingoidSig" -}
record DualdeMorgan : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field prime     : U → U
    field prime-+-*-deMorgan        : ∀ (x y z : U) → prime (x + y) ≡ (prime x) * (prime y)
    field prime-*-+-deMorgan        : ∀ (x y z : U) → prime (x * y) ≡ (prime x) + (prime y)


{- LeftPreSemiring                      = LeftRingoid  union′ Semigroup ⟴  union′ AdditiveCommutativeSemigroup  ⟴ :adjoin-retract₁ nil ⟴ :remark "over RingoidSig" -}
record LeftPreSemiring : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)


{- RightPreSemiring                     = RightRingoid union′  Semigroup ⟴ union′ AdditiveCommutativeSemigroup ⟴ :adjoin-retract₁ nil ⟴ :remark "over RingoidSig" -}
record RightPreSemiring : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)


{- PreSemiring                          = LeftPreSemiring union′ RightRingoid ⟴ :remark "over RingoidSig" -}
record PreSemiring : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- NearSemiring                         = AdditiveSemigroup  union′ Semigroup ⟴ union′ RightRingoid ⟴ :adjoin-retract₁ nil ⟴ :remark "over RingoidSig" -}
record NearSemiring : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- NearSemifield = NearSemiring union′ Group ⟴ :remark "over Semigroup" -}
record NearSemifield : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e


{- Semifield = NearSemifield union′ LeftRingoid ⟴ :remark "over RingoidSig" -}
record Semifield : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field inv       : U → U
    field *-leftInverse     : ∀ (x : U) → x * (inv x) ≡ e
    field *-rightInverse        : ∀ (x : U) → (inv x) * x ≡ e
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)


{- NearRing = AdditiveGroup union′ Semigroup  ⟴ union′ RightRingoid ⟴ :remark "over RingoidSig" -}
record NearRing : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field neg       : U → U
    field +-leftInverse     : ∀ (x : U) → x + (neg x) ≡ 𝟘
    field +-rightInverse        : ∀ (x : U) → (neg x) + x ≡ 𝟘
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- Rng = AbelianAdditiveGroup union′ Semigroup  Ringoid ⟴ :remark "over RingoidSig" -}
record Rng : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field neg       : U → U
    field +-leftInverse     : ∀ (x : U) → x + (neg x) ≡ 𝟘
    field +-rightInverse        : ∀ (x : U) → (neg x) + x ≡ 𝟘
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)


{- Semiring = AdditiveCommutativeMonoid union′  Monoid1 ⟴ union′ Ringoid ⟴ union′ Left0 ⟴ union′ Right0 ⟴ :remark "over Ringoid0Sig" -}
record Semiring : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _*_       : U → U → U
    field 𝟙     : U
    field *-leftIdentity        : ∀ (x : U) → 𝟙 * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * 𝟙 ≡ x
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)
    field *-leftZero        : ∀ (x : U) → 𝟘 * x ≡ 𝟘
    field *-rightZero       : ∀ (x : U) → x * 𝟘 ≡ 𝟘


{- SemiRng       = AdditiveCommutativeMonoid union′ Semigroup ⟴ union′ Ringoid ⟴ :remark "over RingoidSig" -}
record SemiRng : Set₁ where
    field U     : Set
    field _+_       : U → U → U
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _*_       : U → U → U
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- LeftPreDioid  = LeftPreSemiring union′ AdditiveCanonicallyOrderedMonoid ⟴ :remark "over AdditiveMonoid" -}
record LeftPreDioid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)


{- RightPreDioid = RightPreSemiring union′ AdditiveCanonicallyOrderedMonoid ⟴ :remark "over AdditiveMonoid" -}
record RightPreDioid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)


{- PreDioid      = LeftPreDioid union′ RightRingoid ⟴ :remark "over RingoidSig" -}
record PreDioid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)


{- LeftDioid     = LeftPreDioid union′ Monoid ⟴ union′ Left0 ⟴ union′ Right0 ⟴ :remark "over DoubleMonoid" -}
record LeftDioid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-leftZero        : ∀ (x : U) → 𝟘 * x ≡ 𝟘
    field *-rightZero       : ∀ (x : U) → x * 𝟘 ≡ 𝟘


{- RightDioid    = RightPreDioid union′ Monoid ⟴ union′ Left0 ⟴ union′ Right0 ⟴ :remark "over DoubleMonoid" -}
record RightDioid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-leftZero        : ∀ (x : U) → 𝟘 * x ≡ 𝟘
    field *-rightZero       : ∀ (x : U) → x * 𝟘 ≡ 𝟘


{- Dioid         = LeftDioid union′ RightRingoid ⟴ :remark "over RingoidSig" -}
record Dioid : Set₁ where
    field U     : Set
    field _*_       : U → U → U
    field _+_       : U → U → U
    field *-+-leftDistributivity        : ∀ (x y z : U) → x * (y + z) ≡ (x * y) + (x * z)
    field *-associative     : ∀ (x y z : U) → (x * y) * z ≡ x * (y * z)
    field +-associative     : ∀ (x y z : U) → (x + y) + z ≡ x + (y + z)
    field +-commutative     : ∀ (x y : U) → (x + y) ≡ (y + x)
    field _≤_       : U → U → Set
    field +-≤-orderPreserving       : ∀ (x y U v : U) → x ≤ y → (U + (x + v)) ≤ (U + (y + v))
    field ≤-reflexive       : ∀ (x : U) → _≤_ x x
    field ≤-transitive      : ∀ (x y z : U) → _≤_ x y → _≤_ y z → _≤_ x z
    field ≤-antisymmetric       : ∀ (x y : U) → _≤_ y x → _≤_ x y → x ≡ y
    field 𝟘     : U
    field +-leftIdentity        : ∀ (x : U) → 𝟘 + x ≡ x
    field +-rightIdentity       : ∀ (x : U) → x + 𝟘 ≡ x
    field ≤-+-leftCanonicalOrder        : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ a + c)
    field ≤-+-rightCanonicalOrder       : ∀ (a b : U) → (a ≤ b) ↔ (Σ[ c ∈ U ] b ≡ c + a)
    field e     : U
    field *-leftIdentity        : ∀ (x : U) → e * x ≡ x
    field *-rightIdentity       : ∀ (x : U) → x * e ≡ x
    field *-leftZero        : ∀ (x : U) → 𝟘 * x ≡ 𝟘
    field *-rightZero       : ∀ (x : U) → x * 𝟘 ≡ 𝟘
    -- field *-+-rightDistributivity       : ∀ (x y z : U) → (y + z) * x ≡ (y * x) + (z * x)

d = Dioid
