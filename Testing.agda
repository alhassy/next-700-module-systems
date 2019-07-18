{- (load-file "PackageFormer.el") -}

module Testing where

open import Testing_Generated
open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)

{-700
variable
   ℓ : Level

PackageFormer Monoid (v : Variation) : Set where
    _⨾_     : Monoid v → Monoid v → Monoid v
    Id      : Monoid v
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Monoid v} → Id ⨾ x ≡ x
    rightId : ∀ {x : Monoid v} → x ⨾ Id ≡ x


Monoid′  = Monoid opening (MonoidRDT; it ++ "′")
-}

-- MonoidR  = Monoid record unbundling 2

{-
MonoidTypeclass = Monoid typeclass hiding (_⨾_)
MonoidT         = Monoid typeclass renaming (Carrier to C; _⨾_ to _⊕_)
MonoidR         = Monoid record unbundling 2
MonoidE         = Monoid record exposing (Carrier; Id)
MonoidB         = Monoid record with (Carrier to Bool; Id to false)
MonoidD         = Monoid data renaming (_⨾_ to _Δ_)
MonoidD′        = Monoid data decorated ( "╲" ++ it ++ "╱")

-- Accidentally “datar” instead of “data”.
Whoops = Monoid datar

_ = MonoidTypeclass
{- record MonoidTypeclass (Carrier : Set) : Set where … -}

_ = MonoidT ; open MonoidT using (_⊕_)
{- record MonoidT (C : Set) : Set where … -}

_ = MonoidR
{- record MonoidR (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where … -}

_ = MonoidD
{- data MonoidD : Set where … -}

_ = MonoidE
{- record MonoidE (Carrier : Set) (Id : Carrier) : Set where … -}

_ = MonoidB ; open MonoidB using (leftfalse)
{- record MonoidB : Set₀ where … -}

_ = MonoidD′

-}
