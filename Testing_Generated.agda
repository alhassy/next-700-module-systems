{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)
-- It is important to observe that ‘openings’ are lossy:
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


{- MonoidT₂   =  MonoidP typeclass₂ ⟴ :waist-strings ("private" "extra : Set₁" "extra = Set" "field") -}
record MonoidT₂ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where
  private
    extra : Set₁
    extra = Set
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


{- Monoidₘ = MonoidR map₀ :elements (lambda (f) (make-tn (concat (get-name f) "ₘ") (get-type f))) -}
record Monoidₘ : Set₁ where
  field
    Carrierₘ : Set
    _⨾_ₘ : let Carrier = Carrierₘ in Carrier → Carrier → Carrier
    Idₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in Carrier
    assocₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in let Id = Idₘ in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftIdₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in let Id = Idₘ in let assoc = assocₘ in ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightIdₘ : let Carrier = Carrierₘ in let _⨾_ = _⨾_ₘ in let Id = Idₘ in let assoc = assocₘ in let leftId = leftIdₘ in ∀ {x : Carrier} → x ⨾ Id ≡ x


{- Monoidₙ = MonoidR rename₁ :elements (lambda (name) (concat name "ₙ")) -}
record Monoidₙ : Set₁ where
  field
    Carrierₙ : Set
    _⨾ₙ_ : let Carrier = Carrierₙ in Carrier → Carrier → Carrier
    Idₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in Carrier
    assocₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in let Id = Idₙ in ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftIdₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in let Id = Idₙ in let assoc = assocₙ in ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightIdₙ : let Carrier = Carrierₙ in let _⨾_ = _⨾ₙ_ in let Id = Idₙ in let assoc = assocₙ in let leftId = leftIdₙ in ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MR′ = M-Set record ⟴ primer -}
record MR′ : Set₁ where
 field
   Scalar′  : Set
   Vector′  : Set
   _·′_     : Scalar′ → Vector′ → Vector′
   𝟙′       : Scalar′
   _×′_     : Scalar′ → Scalar′ → Scalar′
   leftId′  : {𝓋 : Vector′}  →  𝟙′ ·′ 𝓋  ≡  𝓋
   assoc′   : {a b : Scalar′} {𝓋 : Vector′} → (a ×′ b) ·′ 𝓋  ≡  a ·′ (b ·′ 𝓋)


{- MR₁₋₂    = M-Set record ⟴ decorated :by "₁" ⟴ decorated :by "₂" -}
record MR₁₋₂ : Set₁ where
 field
   Scalar₁₂ : Set
   Vector₁₂ : Set
   _·₁₂_ : Scalar₁₂ → Vector₁₂ → Vector₁₂
   𝟙₁₂ : Scalar₁₂
   _×₁₂_ : Scalar₁₂ → Scalar₁₂ → Scalar₁₂
   leftId₁₂ : {𝓋 : Vector₁₂}  →  𝟙₁₂ ·₁₂ 𝓋  ≡  𝓋
   assoc₁₂ : {a b : Scalar₁₂} {𝓋 : Vector₁₂} → (a ×₁₂ b) ·₁₂ 𝓋  ≡  a ·₁₂ (b ·₁₂ 𝓋)


{- the-MR   = M-Set record ⟴ co-decorated :by "the-" -}
record the-MR : Set₁ where
 field
   the-Scalar : Set
   the-Vector : Set
   _the-·_ : the-Scalar → the-Vector → the-Vector
   the-𝟙 : the-Scalar
   _the-×_ : the-Scalar → the-Scalar → the-Scalar
   the-leftId : {𝓋 : the-Vector}  →  the-𝟙 the-· 𝓋  ≡  𝓋
   the-assoc : {a b : the-Scalar} {𝓋 : the-Vector} → (a the-× b) the-· 𝓋  ≡  a the-· (b the-· 𝓋)


{- MR-oh  = M-Set record ⟴ rename :elements (lambda (name) (pcase name ("Scalar" "S") (x x))) -}
record MR-oh : Set₁ where
 field
   S : Set
   Vector : Set
   _·_ : S → Vector → Vector
   𝟙 : S
   _×_ : S → S → S
   leftId : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc : {a b : S} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- MRₜₒ = M-Set record ⟴ renaming :by "Scalar to S; Vector to V; · to nice" -}
record MRₜₒ : Set₁ where
 field
   S : Set
   V : Set
   _nice_ : S → V → V
   𝟙 : S
   _×_ : S → S → S
   leftId : {𝓋 : V}  →  𝟙 nice 𝓋  ≡  𝓋
   assoc : {a b : S} {𝓋 : V} → (a × b) nice 𝓋  ≡  a nice (b nice 𝓋)


{- MRₜₒ_ = M-Set record ⟴ renaming_ :by "Scalar to S; Vector to V; _·_ to _nice_" -}
record MRₜₒ_ : Set₁ where
 field
   S : Set
   V : Set
   _nice_ : S → V → V
   𝟙 : S
   _×_ : S → S → S
   leftId : {𝓋 : V}  →  𝟙 nice 𝓋  ≡  𝓋
   assoc : {a b : S} {𝓋 : V} → (a × b) nice 𝓋  ≡  a nice (b nice 𝓋)


{- NearMonoid = M-Set record ⟴ renaming :by "Scalar to Carrier; Vector to Carrier; · to ×" -}
record NearMonoid : Set₁ where
 field
   Carrier : Set
   _×_ : Carrier → Carrier → Carrier
   𝟙 : Carrier
   leftId : {𝓋 : Carrier}  →  𝟙 × 𝓋  ≡  𝓋
   assoc : {a b : Carrier} {𝓋 : Carrier} → (a × b) × 𝓋  ≡  a × (b × 𝓋)


{- NearMonoid¹ = M-Set record ⟴ single-sorted :with-sort "Carrier" -}
record NearMonoid¹ : Set₁ where
 field
   Carrier : Set
   _·_ : Carrier → Carrier → Carrier
   𝟙 : Carrier
   _×_ : Carrier → Carrier → Carrier
   leftId : {𝓋 : Carrier}  →  𝟙 · 𝓋  ≡  𝓋
   assoc : {a b : Carrier} {𝓋 : Carrier} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- Neato = M-Set empty-module -}
module Neato (Scalar : Set) (Vector : Set) (_·_ : Scalar → Vector → Vector) (𝟙 : Scalar) (_×_ : Scalar → Scalar → Scalar) (leftId : {𝓋 : Vector} → 𝟙 · 𝓋 ≡ 𝓋) (assoc : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋 ≡ a · (b · 𝓋)) where


{- M-Set-R = M-Set record -}
record M-Set-R : Set₁ where
 field
   Scalar  : Set
   Vector  : Set
   _·_     : Scalar → Vector → Vector
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar
   leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- M-Set-R₁ = M-Set-R open :with (lambda (x) (concat x "₁")) -}
module M-Set-R₁ (ℛ : M-Set-R) where
   
 open M-Set-R ℛ public
     renaming
       ( Scalar to Scalar₁
       ; Vector to Vector₁
       ; _·_ to _·₁_
       ; 𝟙 to 𝟙₁
       ; _×_ to _×₁_
       ; leftId to leftId₁
       ; assoc to assoc₁
       )


{- M-Set-R′ = M-Set-R open-with :decoration "′" -}
module M-Set-R′ (ℛ : M-Set-R) where
   
 open M-Set-R ℛ public
     renaming
       ( Scalar to Scalar′
       ; Vector to Vector′
       ; _·_ to _·′_
       ; 𝟙 to 𝟙′
       ; _×_ to _×′_
       ; leftId to leftId′
       ; assoc to assoc′
       )


{- M-Set-Sorts = M-Set record ⟴ sorts -}
record M-Set-Sorts : Set₁ where
 field
   Scalar  : Set
   Vector  : Set


{- MonoidSignature = M-Set record ⟴ generated :by (lambda (f) (and (s-contains? "Scalar" f) (not (s-contains? "Vector" f)))) -}
record MonoidSignature : Set₁ where
 field
   Scalar  : Set
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar


{- MonSig = M-Set record ⟴ signature -}
record MonSig : Set₁ where
 field
   Scalar  : Set
   Vector  : Set
   _·_     : Scalar → Vector → Vector
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar


{- Hom  = M-Set-R hom -}
record Hom (Src : M-Set-R) (Tgt : M-Set-R) : Set₁ where
 open M-Set-R  Src
 open M-Set-R′ Tgt
 field
   map₁ : Scalar → Scalar′
   map₂ : Vector → Vector′
   pres-· : {x₁ : Scalar} → {x₂ : Vector} →   map₂ (_·_ x₁ x₂)   ≡   _·′_ (map₁ x₁) (map₂ x₂)
   pres-𝟙 : map₁ (𝟙 )   ≡   𝟙′
   pres-× : {x₁ : Scalar} → {x₁ : Scalar} →   map₁ (_×_ x₁ x₁)   ≡   _×′_ (map₁ x₁) (map₁ x₁)


{- Hom² = M-Set-R hom ⟴ renaming :by "map₁ to scalar; pres-𝟙 to unity" -}
record Hom² (Src : M-Set-R) (Tgt : M-Set-R) : Set₁ where
 open M-Set-R  Src
 open M-Set-R′ Tgt
 field
   scalar : Scalar → Scalar′
   map₂ : Vector → Vector′
   pres-· : {x₁ : Scalar} → {x₂ : Vector} →   map₂ (_·_ x₁ x₂)   ≡   _·′_ (scalar x₁) (map₂ x₂)
   unity : scalar (𝟙 )   ≡   𝟙′
   pres-× : {x₁ : Scalar} → {x₁ : Scalar} →   scalar (_×_ x₁ x₁)   ≡   _×′_ (scalar x₁) (scalar x₁)