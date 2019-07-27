{- (load-file "PackageFormer.el") -}

module Testing where
open import Testing_Generated

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)

{-700

variable
   ℓ : Level

PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

-}

{-
𝒱-identity               =
𝒱-record                 = :kind record :waist-strings ("field")
𝒱-whoops                 = :kind recorder :waist-strings ("field")
𝒱-typeclass-attempt      = :kind record :waist-strings ("field") :waist 2
𝒱-typeclass₂             = :kind record :waist-strings ("field") :waist 2 :level dec
𝒱-primed-record          = :kind record :waist-strings ("field") :alter-elements (λ f → (map-name (concat name \"′\") f))
𝒱-primed                 = :alter-elements (λ f → (map-name (concat name "′") f))
𝒱-typeclass height level = :kind record :waist-strings ("field") :waist height :level level
𝒱-data-with carrier      = :kind data :level dec :alter-elements (λ f → (if (s-contains? carrier (target (get-type f))) (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) f) ""))
-}


{-700
MonoidR   =  MonoidP record
MonoidT₂  =  MonoidP typeclass₂
MonoidT₄  =  MonoidP typeclass :height (4) :level (dec)
MonoidD   =  MonoidP data-with :carrier ("Carrier")

-}

{- Click on these, M-., to see the generated code -}
_ = MonoidR
_ = MonoidT₂
_ = MonoidT₄
_ = MonoidD

-- TODO
-- MonoidR′ = MonoidR primed

-- TODO
-- MonoidD′  = MonoidD primed


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
{- TODO: Eventually; after prototype is done. -}











open import Function using (id)
open import Data.List using (List; map)
open import Data.String using () renaming (String to Name)
open import Data.String using () renaming (String to Type)
open import Data.Product using (_×_) renaming (map to bimap)


{- TODO: Eventually; after prototype is done. -}
data VarExpr : Set where
  :kind : String → VarExpr
  :alter-elements : String → VarExpr


{- No lambda's allowed; all arguments must be to the left of the ‘=’. -}
{- Definition must be one liner. -}
𝑽-adorn : List (Name × Type) → (Name → Name) → List (Name × Type)
𝑽-adorn xs f = map (bimap f id) xs

import Data.Maybe as Maybe
open Maybe using (Maybe; just; nothing)
import Data.List as List
open import Data.List using (_++_ ; _∷_)
data Kind : Set where
  ‵data ‵record ‵module ‵function : Kind


record PF : Set where
  field
    kind       : Kind
    name       : Name
    level      : Level
    {- The following four are the “constiutents” or “elements” of a PackageFormer -}
    variation  : Maybe Name
    carrier    : Maybe Name
    parameters : List (Name × Type)
    fields     : List (Name × Type)

{-
pf′ = pf variational (args; otherwise)

variational : (new-name : Name) (args : ⋯) (otherwise : ? → ?) → PF
variational pf′ args otherwise = ???
-}

_Variational₁ : {ℓ : Level} (X : Set ℓ) → Set ℓ
X Variational₁ = (new-name : Name) (to-list : List (Name × X)) (otherwise : Name → X)
               → PF → PF

_Variational₀ : {ℓ : Level} (X : Set ℓ) → Set ℓ
X Variational₀ = (new-name : Name) (to-list : List X) (otherwise : Name → X)
               → PF → PF

open import Data.Product using (_,_)
open import Data.String using (String)
postulate string-replace : (old new : String) → String → String

𝑽-record : Name Variational₁
𝑽-record new-name to-list otherwise pf = let open PF pf in
  record
    { kind       = ‵record
    ; name       = new-name
    ; variation  = nothing
    ; level      = Level.suc level
    ; carrier    = just "Carrier"
    ; parameters = List.[]
    ; fields     =    parameters
                   ++ ("Carrier" , "Set level")  -- HACK!
                   ∷ List.map (bimap (string-replace "name variation" "Carrier") id) fields   -- HACK!
    }

{- This’ a lot at once; let's instead focus on small combinators. -}

-- as-kind : Kind → PF → PF
-- as-kind k

{-
with-carrier : Name → PF → PF
with-carrier c pf = let open PF pf in
  record
    { kind       = kind
    ; name       = name
    ; level      = level
    ; variation  = variation
    ; carrier    = just c
    ; parameters = List.map (bimap f id) parameters
    ; fields     = List.map (bimap f id) fields
    }


alter-elements : (Name → Name) → PF → PF
alter-elements f pf = let open PF pf in
  record
    { kind       = kind
    ; name       = name
    ; level      = level
    ; variation  = variation
    ; carrier    = Maybe.map f carrier
    ; parameters = List.map (bimap f id) parameters
    ; fields     = List.map (bimap f id) fields
    }

-}

{-00

Woah = Monoid record adorn (λ x → x ++ "ₐ")

-}




-- Since seven-hundred comments generate code which is imported, we may use their results
-- seemingly before their definition

-- _ = MonoidR
-- open MonoidR′

{-00
MonoidR   = Monoid record
MonoidR′  = Monoid opening MonoidR (λ x → x ++ "′")
MonoidR₁  = Monoid opening MonoidR (λ x → x ++ "₁")
MonoidR₂  = Monoid opening MonoidR (λ x → x ++ "₂")


record Monoid-Hom (𝒮 𝒯 : MonoidR) : Set where
  open MonoidR₁ 𝒮; open MonoidR₂ 𝒯
  field
    mor     : Carrier₁ → Carrier₂
    id-pres : mor Id₁ ≡ Id₂
    op-pres : ∀ {x y} → mor (x ⨾₁ y) ≡ mor x ⨾₂ mor y
-}

{- Below are other examples, from the past. -}

{-00
MonoidTypeclass = Monoid typeclass hiding (_⨾_)
MonoidT         = Monoid typeclass renaming (Carrier to C; _⨾_ to _⊕_)
MonoidE         = Monoid record exposing (Carrier; Id)
MonoidB         = Monoid record with (Carrier to Bool; Id to false)
MonoidD         = Monoid data renaming (_⨾_ to _Δ_)


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

-}
