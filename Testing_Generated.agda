{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as Level
module Testing_Generated where
open import Testing_Generated_Generated
variable
   ℓ : Level

{- MonoidR  = Monoid record unbundling 2 -}
record MonoidR (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where
  field
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

Monoid′ = {! Variation ‘opening’ not yet supported !}

module Semantics₁ (ℛ : MonoidR ? ?) where
    open MonoidR ℛ public
         renaming
           ( rightId to rightId′
           ; leftId to leftId′
           ; assoc to assoc′
           ; Id to Id′
           ; _⨾_ to _⨾′_
           ; Carrier to Carrier′
           )
