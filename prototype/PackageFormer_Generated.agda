{- This file is generated ;; do not alter. -}

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)
open import Level as Level
module PackageFormer_Generated where 


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer MonoidP : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}





{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 

PackageFormer M-Set : Set₁ where
   Scalar       : Set
   Vector       : Set
   _·_      : Scalar → Vector → Vector
   𝟙        : Scalar
   _×_      : Scalar → Scalar → Scalar
   leftId       : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc        : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidPⁱᵈ = MonoidP identity -}
PackageFormer MonoidPⁱᵈ : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidP⁰  = MonoidP -}
PackageFormer MonoidP⁰ : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- MonoidPᶜ = MonoidP ⟴ -}
PackageFormer MonoidPᶜ : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- Monoid-test = MonoidP ⟴ test "positional arg₁" "positional arg₂" :keyword 25 -}
PackageFormer Monoid-test : Set₁ where
    Carrier     : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc       : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId      : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId     : ∀ {x : Carrier} → x ⨾ Id ≡ x -}


{- M-Set-Record = M-Set record -}
record M-Set-Record : Set₁ where
   field Scalar     : Set
   field Vector     : Set
   field _·_        : Scalar → Vector → Vector
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- M-Set-TypeClass = M-Set typeclass-attempt -}
record M-Set-TypeClass (Scalar : Set) (Vector : Set) : Set₁ where
   field _·_        : Scalar → Vector → Vector
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- MonoidT₂      = MonoidP typeclass₂ -}
record MonoidT₂ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) : Set where
    field Id        : Carrier
    field assoc     : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    field leftId        : ∀ {x : Carrier} → Id ⨾ x ≡ x
    field rightId       : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MonoidT₃         = MonoidP record ⟴ :waist 3 :level dec -}
record MonoidT₃ (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) (Id : Carrier) : Set where
    field assoc     : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    field leftId        : ∀ {x : Carrier} → Id ⨾ x ≡ x
    field rightId       : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- M-Set-Typeclass₂ = M-Set record ⟴ typeclass₂ -}
record M-Set-Typeclass₂ (Scalar : Set) (Vector : Set) : Set where
   field _·_        : Scalar → Vector → Vector
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- MonoidT₃-again = MonoidP ⟴ record ⟴ exposing 3 -}
record MonoidT₃-again (Carrier : Set) (_⨾_ : Carrier → Carrier → Carrier) (Id : Carrier) : Set₁ where
    field assoc     : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    field leftId        : ∀ {x : Carrier} → Id ⨾ x ≡ x
    field rightId       : ∀ {x : Carrier} → x ⨾ Id ≡ x


{- MR′ = M-Set record ⟴ primer -}
record MR′ : Set₁ where
   field Scalar′        : Set
   field Vector′        : Set
   field _·′_       : Scalar′ → Vector′ → Vector′
   field 𝟙′     : Scalar′
   field _×′_       : Scalar′ → Scalar′ → Scalar′
   field leftId′        : {𝓋 : Vector′}  →  𝟙′ ·′ 𝓋  ≡  𝓋
   field assoc′     : {a b : Scalar′} {𝓋 : Vector′} → (a ×′ b) ·′ 𝓋  ≡  a ·′ (b ·′ 𝓋)


{- Kind “PackageFormer” does not correspond  to a concrete Agda type. 
{- M-Set′-attempt-raw = M-Set primed-attempt -}
PackageFormer M-Set′-attempt-raw : Set₁ where
   Scalar′      : Set
   Vector′      : Set
   _·′_     : Scalar → Vector → Vector
   𝟙′       : Scalar
   _×′_     : Scalar → Scalar → Scalar
   leftId′      : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc′       : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) -}


{- M-Set2-Typeclass₃ = M-Set typeclass 3 :level 'inc -}
record M-Set2-Typeclass₃ (Scalar : Set) (Vector : Set) (_·_ : Scalar → Vector → Vector) : Set₂ where
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- M-Set0-Typeclass₃ = M-Set typeclass 3 -}
record M-Set0-Typeclass₃ (Scalar : Set) (Vector : Set) (_·_ : Scalar → Vector → Vector) : Set where
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- MR𝕏    = M-Set record ⟴ map (λ e → (map-name (λ n → (rename-mixfix (λ x → (concat x "𝕏")) n)) e)) -}
record MR𝕏 : Set₁ where
   field Scalar𝕏        : Set
   field Vector𝕏        : Set
   field _·𝕏_       : Scalar𝕏 → Vector𝕏 → Vector𝕏
   field 𝟙𝕏     : Scalar𝕏
   field _×𝕏_       : Scalar𝕏 → Scalar𝕏 → Scalar𝕏
   field leftId𝕏        : {𝓋 : Vector𝕏}  →  𝟙𝕏 ·𝕏 𝓋  ≡  𝓋
   field assoc𝕏     : {a b : Scalar𝕏} {𝓋 : Vector𝕏} → (a ×𝕏 b) ·𝕏 𝓋  ≡  a ·𝕏 (b ·𝕏 𝓋)


{- MR𝕪    = M-Set record ⟴ rename (λ n → (concat n "𝕪")) -}
record MR𝕪 : Set₁ where
   field Scalar𝕪        : Set
   field Vector𝕪        : Set
   field _·𝕪_       : Scalar𝕪 → Vector𝕪 → Vector𝕪
   field 𝟙𝕪     : Scalar𝕪
   field _×𝕪_       : Scalar𝕪 → Scalar𝕪 → Scalar𝕪
   field leftId𝕪        : {𝓋 : Vector𝕪}  →  𝟙𝕪 ·𝕪 𝓋  ≡  𝓋
   field assoc𝕪     : {a b : Scalar𝕪} {𝓋 : Vector𝕪} → (a ×𝕪 b) ·𝕪 𝓋  ≡  a ·𝕪 (b ·𝕪 𝓋)


{- MR-oh  = M-Set record ⟴ rename (λ n → (pcase n ("Scalar" "S") ("𝟙" "ε") (else else))) -}
record MR-oh : Set₁ where
   field S      : Set
   field Vector     : Set
   field _·_        : S → Vector → Vector
   field ε      : S
   field _×_        : S → S → S
   field leftId     : {𝓋 : Vector}  →  ε · 𝓋  ≡  𝓋
   field assoc      : {a b : S} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- MR₁₂   = M-Set record ⟴ decorated "₁" ⟴ decorated "₂" -}
record MR₁₂ : Set₁ where
   field Scalar₁₂       : Set
   field Vector₁₂       : Set
   field _·₁₂_      : Scalar₁₂ → Vector₁₂ → Vector₁₂
   field 𝟙₁₂        : Scalar₁₂
   field _×₁₂_      : Scalar₁₂ → Scalar₁₂ → Scalar₁₂
   field leftId₁₂       : {𝓋 : Vector₁₂}  →  𝟙₁₂ ·₁₂ 𝓋  ≡  𝓋
   field assoc₁₂        : {a b : Scalar₁₂} {𝓋 : Vector₁₂} → (a ×₁₂ b) ·₁₂ 𝓋  ≡  a ·₁₂ (b ·₁₂ 𝓋)


{- the-MR = M-Set record ⟴ co-decorated "the-" -}
record the-MR : Set₁ where
   field the-Scalar     : Set
   field the-Vector     : Set
   field _the-·_        : the-Scalar → the-Vector → the-Vector
   field the-𝟙      : the-Scalar
   field _the-×_        : the-Scalar → the-Scalar → the-Scalar
   field the-leftId     : {𝓋 : the-Vector}  →  the-𝟙 the-· 𝓋  ≡  𝓋
   field the-assoc      : {a b : the-Scalar} {𝓋 : the-Vector} → (a the-× b) the-· 𝓋  ≡  a the-· (b the-· 𝓋)


{- MR₃₄   = M-Set record ⟴ subscripted₃ ⟴ subscripted₄ -}
record MR₃₄ : Set₁ where
   field Scalar₃₄       : Set
   field Vector₃₄       : Set
   field _·₃₄_      : Scalar₃₄ → Vector₃₄ → Vector₃₄
   field 𝟙₃₄        : Scalar₃₄
   field _×₃₄_      : Scalar₃₄ → Scalar₃₄ → Scalar₃₄
   field leftId₃₄       : {𝓋 : Vector₃₄}  →  𝟙₃₄ ·₃₄ 𝓋  ≡  𝓋
   field assoc₃₄        : {a b : Scalar₃₄} {𝓋 : Vector₃₄} → (a ×₃₄ b) ·₃₄ 𝓋  ≡  a ·₃₄ (b ·₃₄ 𝓋)


{- MRₜₒ   = M-Set record ⟴ renaming "Scalar to S; Vector to V; · to nice" -}
record MRₜₒ : Set₁ where
   field S      : Set
   field V      : Set
   field _nice_     : S → V → V
   field 𝟙      : S
   field _×_        : S → S → S
   field leftId     : {𝓋 : V}  →  𝟙 nice 𝓋  ≡  𝓋
   field assoc      : {a b : S} {𝓋 : V} → (a × b) nice 𝓋  ≡  a nice (b nice 𝓋)


{- NearMonoid = M-Set record ⟴ renaming "Scalar to Carrier; Vector to Carrier; · to ×" -}
record NearMonoid : Set₁ where
   field Carrier        : Set
   field _×_        : Carrier → Carrier → Carrier
   field 𝟙      : Carrier
   field leftId     : {𝓋 : Carrier}  →  𝟙 × 𝓋  ≡  𝓋
   field assoc      : {a b : Carrier} {𝓋 : Carrier} → (a × b) × 𝓋  ≡  a × (b × 𝓋)


{- NearMonoid¹ = M-Set record ⟴ single-sorted "Carrier" -}
record NearMonoid¹ : Set₁ where
   field Carrier        : Set
   field _·_        : Carrier → Carrier → Carrier
   field 𝟙      : Carrier
   field _×_        : Carrier → Carrier → Carrier
   field leftId     : {𝓋 : Carrier}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Carrier} {𝓋 : Carrier} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- Neato = M-Set empty-module -}
module Neato (Scalar : Set) (Vector : Set) (_·_ : Scalar → Vector → Vector) (𝟙 : Scalar) (_×_ : Scalar → Scalar → Scalar) (leftId : {𝓋 : Vector} → 𝟙 · 𝓋 ≡ 𝓋) (assoc : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋 ≡ a · (b · 𝓋)) where


{- M-Set-R = M-Set record -}
record M-Set-R : Set₁ where
   field Scalar     : Set
   field Vector     : Set
   field _·_        : Scalar → Vector → Vector
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar
   field leftId     : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   field assoc      : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)


{- M-Set-R₁ = M-Set-R ⟴ open (λ x → (concat x "₁")) -}
module M-Set-R₁ (Arg7626 : M-Set-R) where
   Scalar₁      : let open M-Set-R Arg7626 in Set ; Scalar₁ = M-Set-R.Scalar Arg7626
   Vector₁      : let open M-Set-R Arg7626 in Set ; Vector₁ = M-Set-R.Vector Arg7626
   _·₁_     : let open M-Set-R Arg7626 in Scalar → Vector → Vector ;    _·₁_ = M-Set-R._·_ Arg7626
   𝟙₁       : let open M-Set-R Arg7626 in Scalar ;  𝟙₁ = M-Set-R.𝟙 Arg7626
   _×₁_     : let open M-Set-R Arg7626 in Scalar → Scalar → Scalar ;    _×₁_ = M-Set-R._×_ Arg7626
   leftId₁      : let open M-Set-R Arg7626 in {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋 ;    leftId₁ = M-Set-R.leftId Arg7626
   assoc₁       : let open M-Set-R Arg7626 in {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) ;   assoc₁ = M-Set-R.assoc Arg7626


{- M-Set-R-SV = M-Set-R opening "Scalar to S; Vector to V" -}
module M-Set-R-SV (Arg7627 : M-Set-R) where
   S        : let open M-Set-R Arg7627 in Set ; S = M-Set-R.Scalar Arg7627
   V        : let open M-Set-R Arg7627 in Set ; V = M-Set-R.Vector Arg7627
   _        : let open M-Set-R Arg7627 in Scalar → Vector → Vector ;    _ = M-Set-R._·_ Arg7627
   _        : let open M-Set-R Arg7627 in Scalar ;  _ = M-Set-R.𝟙 Arg7627
   _        : let open M-Set-R Arg7627 in Scalar → Scalar → Scalar ;    _ = M-Set-R._×_ Arg7627
   _        : let open M-Set-R Arg7627 in {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋 ;    _ = M-Set-R.leftId Arg7627
   _        : let open M-Set-R Arg7627 in {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) ;   _ = M-Set-R.assoc Arg7627


{- M-Set-Sorts = M-Set record ⟴ sorts -}
record M-Set-Sorts : Set₁ where
   field Scalar     : Set
   field Vector     : Set


{- MonoidSignature = M-Set record ⟴ generated (λ e → (and (s-contains? "Scalar" (element-type e)) (not (s-contains? "Vector" (element-type e))))) -}
record MonoidSignature : Set₁ where
   field Scalar     : Set
   field 𝟙      : Scalar
   field _×_        : Scalar → Scalar → Scalar


{- M-Set-R′ = M-Set-R open-with-decoration "′" -}
module M-Set-R′ (Arg7628 : M-Set-R) where
   Scalar′      : let open M-Set-R Arg7628 in Set ; Scalar′ = M-Set-R.Scalar Arg7628
   Vector′      : let open M-Set-R Arg7628 in Set ; Vector′ = M-Set-R.Vector Arg7628
   _·′_     : let open M-Set-R Arg7628 in Scalar → Vector → Vector ;    _·′_ = M-Set-R._·_ Arg7628
   𝟙′       : let open M-Set-R Arg7628 in Scalar ;  𝟙′ = M-Set-R.𝟙 Arg7628
   _×′_     : let open M-Set-R Arg7628 in Scalar → Scalar → Scalar ;    _×′_ = M-Set-R._×_ Arg7628
   leftId′      : let open M-Set-R Arg7628 in {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋 ;    leftId′ = M-Set-R.leftId Arg7628
   assoc′       : let open M-Set-R Arg7628 in {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋) ;   assoc′ = M-Set-R.assoc Arg7628