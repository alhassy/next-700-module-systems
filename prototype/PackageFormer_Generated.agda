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


{- ScalarTerm = M-Set data "Scalar" -}
data ScalarTerm : Set where
   𝟙        : ScalarTerm
   _×_      : ScalarTerm → ScalarTerm → ScalarTerm