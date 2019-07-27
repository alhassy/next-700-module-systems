{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)
open import Function using (id)
open import Data.List using (List; map)
open import Data.String using () renaming (String to Name)
open import Data.String using () renaming (String to Type)
open import Data.Product using (_×_) renaming (map to bimap)
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

{- MonoidR   =  MonoidP record -}
record MonoidR : Set₁ where
  field
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

{- MonoidT₂  =  MonoidP typeclass₂ -}
record MonoidT₂ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where
  field
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

{- MonoidT₄  =  MonoidP typeclass :height (4) :level (dec) -}
record MonoidT₄ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) (Id : Carrier) (assoc : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)) : Set where
  field
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

{- MonoidD   =  MonoidP data-with :carrier ("Carrier") -}
data MonoidD : Set where
    
    _⨾_ : MonoidD → MonoidD → MonoidD
    Id : MonoidD
    
    
    