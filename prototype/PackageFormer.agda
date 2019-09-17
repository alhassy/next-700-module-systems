{- This loads the PackageFormer metaprogram          -}
{- (progn (load-file "PackageFormer.el") (700-mode)) -}

module PackageFormer where

open import PackageFormer_Generated
open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)

{-
0. There are a number of common use-cases.
1. We can handle all of them & more, since we're extensible.
  - Mention the Lean & Coq, as well as the Agda, repeated fragments.
2. The resulting setup is pragmatic: It is unobtrusive in the
   traditional Agda coding style in that it happens in the background.
3. It fills a particular need; the desire to avoid repetitious code.
-}

{- lisp
(message-box "Hello")
(message-box "World")
-}

{-700
PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

PackageFormer M-Set : Set₁ where
   Scalar  : Set
   Vector  : Set
   _·_     : Scalar → Vector → Vector
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar
   leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)

-}

{-700
-- Variational with empty right hand side.
𝒱-identity =
-}

{-700
MonoidPⁱᵈ = MonoidP identity
-}

{-700
𝒱-no-op = "This is the do-nothing variational"
-}

{-700
-- No variational clauses needed!
MonoidP⁰  = MonoidP
-}

{-700
-- Identity of composition ⟴
MonoidPᶜ = MonoidP ⟴
-}

{-700
𝒱-test positional (keyword 3) another = "I have two mandatory arguments and one keyword argument"

Monoid-test = MonoidP ⟴ test "positional arg₁" "positional arg₂" :keyword 25
-}

{-   700
𝒱-whoops  = tester 1 2 :keyword 3
-}

{-700
𝒱-record = :kind record :alter-elements (λ es → (--map (map-qualifier (λ _ → "field") it) es))
-}

{-700
M-Set-Record = M-Set record
-}

{-lisp
(𝒱 record = "Reify a variational as an Agda “record”."
            :kind record
            :alter-elements (λ es → (--map (map-qualifier (λ _ → "field") it) es)))
-}

{-700
𝒱-typeclass-attempt = record ⟴ :waist 2
-}

{-700
M-Set-TypeClass = M-Set typeclass-attempt
-}

{-700
𝒱-typeclass₂ = record ⟴ :waist 2 :level dec
MonoidT₂      = MonoidP typeclass₂
-}

{-700
MonoidT₃         = MonoidP record ⟴ :waist 3 :level dec
M-Set-Typeclass₂ = M-Set record ⟴ typeclass₂
-}

{-700
MonoidT₃-again = MonoidP ⟴ record ⟴ exposing 3
-}

{-700
-- Intensionally erroenous attempt.
𝒱-primed-attempt = :alter-elements (λ es → (--map (map-name (λ n → (rename-mixfix (λ op → (concat op "′")) n)) it) es))

-- M-Set′-attempt = M-Set record ⟴ primed-attempt
-}

{-lisp
(𝒱 primer = :alter-elements (lambda (es)
   (let* ((esnew es)
         ;; Let's try to accomodate for names with underscores
         (names_ (--map (element-name it) es))
         (names  (--map (s-replace "_" "" it) names_))
         (oldies (append names names_)))

     (loop for old in oldies
           for new in (--map (rename-mixfix (λ n → (concat n "′")) it) oldies)
           do
           (setq esnew (--map (element-replace old new it) esnew)))

     ;; return value
     esnew)))
-}

{-700
MR′ = M-Set record ⟴ primer
-}

{-700
M-Set′-attempt-raw = M-Set primed-attempt
-}

{-700
𝒱-typeclass height (level 'dec) = record ⟴ :waist height :level level
M-Set2-Typeclass₃ = M-Set typeclass 3 :level 'inc
M-Set0-Typeclass₃ = M-Set typeclass 3
-}

{-700
MR𝕏    = M-Set record ⟴ map (λ e → (map-name (λ n → (rename-mixfix (λ x → (concat x "𝕏")) n)) e))
-}

{-700
MR𝕪    = M-Set record ⟴ rename (λ n → (concat n "𝕪"))
MR-oh  = M-Set record ⟴ rename (λ n → (pcase n ("Scalar" "S") ("𝟙" "ε") (else else)))
-}

{-700
MR₁₂   = M-Set record ⟴ decorated "₁" ⟴ decorated "₂"
the-MR = M-Set record ⟴ co-decorated "the-"
MR₃₄   = M-Set record ⟴ subscripted₃ ⟴ subscripted₄
MRₜₒ   = M-Set record ⟴ renaming "Scalar to S; Vector to V; · to nice"
NearMonoid = M-Set record ⟴ renaming "Scalar to Carrier; Vector to Carrier; · to ×"
-}

{-700
NearMonoid¹ = M-Set record ⟴ single-sorted "Carrier"
-}

{-   700
ScalarTerm = M-Set data "Scalar"
-}
