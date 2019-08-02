{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)
-- The name “_×_” is in scope since I've imported Data.Product down below for some
open import Function using (id)
open import Data.List using (List; map)
open import Data.String using () renaming (String to Name)
open import Data.String using () renaming (String to Type)
-- open import Data.Product using (_×_) renaming (map to bimap)
import Data.Maybe as Maybe
import Data.List as List
open import Data.List using (_++_ ; _∷_)
open import Data.Product using (_,_)
open import Data.String using (String)
-- Since seven-hundred comments generate code which is imported, we may use their results
open import Level as Level
module Testing_Generated where 

variable
   ℓ : Level
{- Kind “PackageFormer” does not correspond to a concrete Agda type. 

PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond to a concrete Agda type. 

PackageFormer M-Set : Set₁ where
   Scalar  : Set
   Vector  : Set
   _·_     : Scalar → Vector → Vector
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar
   leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) -}


{- Kind “PackageFormer” does not correspond to a concrete Agda type. 
{- MonoidPⁱᵈ = MonoidP identity -}
PackageFormer MonoidPⁱᵈ : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond to a concrete Agda type. 
{- MonoidP⁰  = MonoidP -}
PackageFormer MonoidP⁰ : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond to a concrete Agda type. 
{- MonoidPᶜ = MonoidP ⟴ -}
PackageFormer MonoidPᶜ : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- MonoidT₃   =  MonoidP record ⟴ :waist 3 :level dec -}
record MonoidT₃ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) (Id : Carrier) : Set where
  field
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MonoidT₂   =  MonoidP typeclass₂ -}
record MonoidT₂ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where
  field
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MonoidT₄   =  MonoidP typeclass :height 4 :level 'dec -}
record MonoidT₄ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) (Id : Carrier) (assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)) : Set where
  field
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- M-Set-Record = M-Set record -}
record M-Set-Record : Set₁ where
 field
   Scalar  : Set
   Vector  : Set
   _·_     : Scalar → Vector → Vector
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar
   leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- M-Set-Typeclass₃ = M-Set-Record typeclass :height 3 :level 'dec -}
record M-Set-Typeclass₃ (Scalar : Set) (Vector : Set) (_·_ : Scalar → Vector → Vector) : Set where
 field
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar
   leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- Kind “PackageFormer” does not correspond to a concrete Agda type. 
{- M-Set′-attempt = M-Set primed-attempt -}
PackageFormer M-Set′-attempt : Set₁ where
   Scalar′ : Set
   Vector′ : Set
   _·′_ : Scalar → Vector → Vector
   𝟙′ : Scalar
   _×′_ : Scalar → Scalar → Scalar
   leftId′ : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc′ : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) -}


{- MonoidR    =  MonoidP record -}
record MonoidR : Set₁ where
  field
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MonoidR′   =  MonoidP record ⟴ primedₗₑₜ -}
record MonoidR′ : Set₁ where
  field
    Carrier′ : Set
    _⨾′_ : let Carrier = Carrier′ in Carrier → Carrier → Carrier
    Id′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in Carrier
    assoc′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in let Id = Id′ in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in let Id = Id′ in let assoc = assoc′ in ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in let Id = Id′ in let assoc = assoc′ in let leftId = leftId′ in ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MonoidR″   =  MonoidR primedₗₑₜ -}
record MonoidR″ : Set₁ where
  field
    Carrier′ : Set
    _⨾′_ : let Carrier = Carrier′ in Carrier → Carrier → Carrier
    Id′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in Carrier
    assoc′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in let Id = Id′ in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in let Id = Id′ in let assoc = assoc′ in ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId′ : let Carrier = Carrier′ in let _⨾_ = _⨾′_ in let Id = Id′ in let assoc = assoc′ in let leftId = leftId′ in ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MR′ = M-Set record ⟴ primer -}
record MR′ : Set₁ where
 field


{- Monoidₘ = MonoidR map :elements (lambda (f) (make-tn (concat (get-name f) "ₘ") (get-type f))) -}
record Monoidₘ : Set₁ where
  field
    Carrierₘ : Set
    _⨾_ₘ : let Carrier = Carrierₘ in Carrier → Carrier → Carrier
    Idₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in Carrier
    assocₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in let Id = Idₘ in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftIdₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in let Id = Idₘ in let assoc = assocₘ in ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightIdₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in let Id = Idₘ in let assoc = assocₘ in let leftId = leftIdₘ in ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoidₙ = MonoidR rename :elements (lambda (name) (concat name "ₙ")) -}
record Monoidₙ : Set₁ where
  field
    Carrierₙ : Set
    _⨾ₙ_ : let Carrier = Carrierₙ in Carrier → Carrier → Carrier
    Idₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in Carrier
    assocₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in let Id = Idₙ in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftIdₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in let Id = Idₙ in let assoc = assocₙ in ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightIdₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in let Id = Idₙ in let assoc = assocₙ in let leftId = leftIdₙ in ∀ {x : Carrier} → x ⨾ Id ≡ x