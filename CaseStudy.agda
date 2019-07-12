{- (load-file "PackageFormer.el") -}

module CaseStudy where
open import CaseStudy_Generated
open import Level
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- To make the exposition easier to read.
   The ‘???’ is whatever the user whishes to
   accomplish in the task at hand; i.e., it's a hole.
-}
postulate ??? : ∀ {ℓ} {A : Set ℓ} → A

{-700
variable
   ℓ : Level

PackageFormer Monoid (v : Variation) : Set where
    _⨾_     : Monoid v → Monoid v → Monoid v
    Id      : Monoid v
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Monoid v} → Id ⨾ x ≡ x
    rightId : ∀ {x : Monoid v} → x ⨾ Id ≡ x

Classical = Monoid typeclass
MonoidOp = Monoid record unbundling 2
MonoidId = Monoid record exposing (Carrier; Id)
Monoid-false = Monoid record with (Carrier to 𝔹; Id to false)

Monoid-m = Monoid typeclass renaming (Carrier to m)
-}

{- M-. on these to see their elaborated forms. -}
_ = Classical
_ = MonoidOp
_ = MonoidId

open Classical using () renaming (_⨾_ to Op)

yuck-one :    (X Y : Classical 𝔹)
         →  Op X  ≡ _∧_
         →  Op Y  ≡ _∨_
         →  Set
yuck-one = ???

first-problem : MonoidOp 𝔹 _∧_  →  MonoidOp 𝔹 _∨_  → Set
first-problem = ???

second-problem-okay : (X Y : MonoidId 𝔹 false) → Set
second-problem-okay = ???

second-problem-better : (X Y : Monoid-false) → Set
second-problem-better = ???
