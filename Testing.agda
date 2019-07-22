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
-}


{- Since 700-comments generate code which is imported, we may use their results
   seemingly before their definition -}

_ = MonoidR
open MonoidR′

{-700
MonoidR   = Monoid record
MonoidR′  = Monoid opening MonoidR (λ x → x ++ "′")
MonoidR₁  = Monoid opening MonoidR (λ x → x ++ "₁")
MonoidR₂  = Monoid opening MonoidR (λ x → x ++ "₂")
-}

record Monoid-Hom (𝒮 𝒯 : MonoidR) : Set where
  open MonoidR₁ 𝒮; open MonoidR₂ 𝒯
  field
    mor     : Carrier₁ → Carrier₂
    id-pres : mor Id₁ ≡ Id₂
    op-pres : ∀ {x y} → mor (x ⨾₁ y) ≡ mor x ⨾₂ mor y

{- Below are other examples, from the past. -}

{-700
MonoidTypeclass = Monoid typeclass hiding (_⨾_)
MonoidT         = Monoid typeclass renaming (Carrier to C; _⨾_ to _⊕_)
MonoidE         = Monoid record exposing (Carrier; Id)
MonoidB         = Monoid record with (Carrier to Bool; Id to false)
MonoidD         = Monoid data renaming (_⨾_ to _Δ_)
-}

-- MonoidR         = Monoid record unbundling 2
-- MonoidD′        = Monoid data decorated (λ it → "╲" ++ it ++ "╱")

-- Accidentally “datar” instead of “data”.
-- Whoops = Monoid datar

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

-- _ = MonoidD′
