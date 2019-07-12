{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as Level
module Testing_Generated where 
variable
   ℓ : Level

{- MonoidTypeclass = Monoid typeclass hiding (_⨾_) -}
record MonoidTypeclass (Carrier : Set) : Set where
  field
    Id      : Carrier

{- MonoidT = Monoid typeclass renaming (Carrier to C; _⨾_ to _⊕_) -}
record MonoidT (C : Set) : Set where
  field
    _⊕_     : let Carrier = C in C → C → C
    Id      : let Carrier = C in C
    assoc   : let _⨾_ = _⊕_ in let Carrier = C in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : let _⨾_ = _⊕_ in let Carrier = C in ∀ {x : let _⨾_ = _⊕_ in let Carrier = C in C} → Id ⨾ x ≡ x
    rightId : let _⨾_ = _⊕_ in let Carrier = C in ∀ {x : let _⨾_ = _⊕_ in let Carrier = C in C} → x ⨾ Id ≡ x

{- MonoidR = Monoid record unbundling 2 -}
record MonoidR (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where
  field
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

{- MonoidE = Monoid record exposing (Carrier; Id) -}
record MonoidE (Carrier : Set) (Id : Carrier) : Set where
  field
    _⨾_     : Carrier → Carrier → Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

{- MonoidB = Monoid record with (Carrier to Bool; Id to false) -}
record MonoidB : Set where
  field
    _⨾_     : Bool → Bool → Bool
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftfalse  : ∀ {x : Bool} → false ⨾ x ≡ x
    rightfalse : ∀ {x : Bool} → x ⨾ false ≡ x

{- MonoidD = Monoid data renaming (_⨾_ to _Δ_) -}
data MonoidD : Set where
    _Δ_     : MonoidD → MonoidD → MonoidD
    Id      : let _⨾_ = _Δ_ in MonoidD