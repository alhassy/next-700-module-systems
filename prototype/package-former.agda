{- This loads the PackageFormer metaprogram; press C-x C-e after the closing “)” below.                 -}
{- (progn (load-file "~/.emacs.d/agda-next-700-module-systems.el") (agda-next-700-module-systems-mode)) -}

module package-former where

open import package-former-generated
open import Level
open import Data.Bool
open import Data.List using (List; _∷_; []; foldr)
import Relation.Binary.PropositionalEquality as ≡; open ≡ using (_≡_)


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
PackageFormer MonoidP : Set₁ where

    -- A few declarations
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

    -- We have a setoid-like structure; with a default implementation
    _≈_   : Carrier → Carrier → Set
    _≈_   = _≡_
    ⨾-cong : ∀ {x y x′ y′} → x ≈ x′ →  y ≈ y′ → (x ⨾ y) ≈ (x′ ⨾ y′)
    ⨾-cong = λ{ ≡.refl ≡.refl → ≡.refl}

    -- For now only one item in a declaration;
    -- namely “Lid” & “Rid” cannot be declared in one line.
    Lid : Carrier → Carrier
    Lid x = Id ⨾ x
    Rid : Carrier → Carrier
    Rid x = x ⨾ Id

    -- Agda permits pure, non-pattern-matching, equations between “fields” in a record.
    concat : List Carrier → Carrier
    concat = foldr _⨾_ Id

    -- More declarations
    leftId  : ∀ {x : Carrier} → (Id ⨾ x) ≈ x
    rightId : ∀ {x : Carrier} → Rid x ≈ x

    -- Since there are no more pure declarations, “fields”, subsequent equations
    -- may use pattern matching.

    Id² : (Id ⨾ Id) ≈ Id
    Id² = rightId

    concatₚ : List Carrier → Carrier
    concatₚ []       = Id
    concatₚ (x ∷ xs) = x ⨾ concatₚ xs
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
𝒱-record₀ = :kind record :alter-elements (λ es → (--map (map-qualifier (λ _ → "field") it) es))
-}

{-
M-Set-Record = M-Set record₀
-}

{-lisp
(𝒱 record₁ (discard-equations nil)
 = "Reify a variational as an Agda “record”.
    Elements with equations are construed as
    derivatives of fields  ---the elements
    without any equations--- by default, unless
    DISCARD-EQUATIONS is provided with a non-nil value.
   "
  :kind record
  :alter-elements
    (λ es →
      (thread-last es
      ;; Keep or drop eqns depending on “discard-equations”
      (--map
        (if discard-equations
            (map-equations (λ _ → nil) it)
            it))
      ;; Unless there's equations, mark elements as fields.
      (--map (map-qualifier
        (λ _ → (unless (element-equations it)
               "field")) it)))))
-}

{-700
Monoid-Record-derived = MonoidP record₁
-}

{-
Monoid-Record-field = MonoidP record₁ :discard-equations t
-}

{-
Monoid-Record-derived-again  = MonoidP record
Monoid-Record-derived-again2 = MonoidP record :and-names t
Monoid-Record-field-again    = MonoidP record :discard-equations t
Monoid-Record-no-equationals = MonoidP record :discard-equations t :and-names t
-}

{-
𝒱-typeclass-attempt = record ⟴ :waist 2
-}

{-
M-Set-TypeClass = M-Set typeclass-attempt
-}

{-
𝒱-typeclass₂ = record ⟴ :waist 2 :level dec
MonoidT₂      = MonoidP typeclass₂
-}

{-
MonoidT₃         = MonoidP record ⟴ :waist 3 :level dec
-- MonoidT₃-again   = MonoidP ⟴ record ⟴ unbundling 3
M-Set-Typeclass₂ = M-Set record ⟴ typeclass₂
-}

{-
-- Ill-formed in Agda: A defintion is not a parameter!
MonoidP-Typeclass₅ = MonoidP :waist 5
-}

{-
MonoidT₅ = MonoidP ⟴ unbundling 5 ⟴ record
-}

{-
-- Intentionally erroenous attempt.
𝒱-primed-attempt = :alter-elements (λ es → (--map (map-name (λ n → (rename-mixfix (λ np → (concat np "′")) n)) it) es))

-- M-Set′-attempt = M-Set record ⟴ primed-attempt
-}

{-
M-Set′-attempt-raw = M-Set primed-attempt
-}

{-
𝒱-typeclass height (level 'dec) = record ⟴ :waist height :level level
M-Set2-Typeclass₃ = M-Set typeclass 3 :level 'inc
M-Set0-Typeclass₃ = M-Set typeclass 3
-}

{-
MR𝕏    = M-Set record ⟴ map (λ e → (map-name (λ n → (rename-mixfix (λ x → (concat x "𝕏")) n)) e))
-}

{-
MR𝕪    = M-Set-Record rename (λ n → (concat n "𝕪"))
MR-oh  = M-Set-Record rename (λ n → (pcase n ("Scalar" "S") ("𝟙" "ε") (else else)))
-}

{-
-- MR₁₂   = M-Set-Record decorated "₁" ⟴ decorated "₂" :adjoin-retract nil
the-MR = M-Set-Record co-decorated "the-"
-- MR₃₄   = M-Set-Record subscripted₃ ⟴ subscripted₄ :adjoin-retract nil
MRₜₒ   = M-Set-Record renaming "Scalar to S; Vector to V; · to nice"
NearMonoid = M-Set-Record renaming "Scalar to Carrier; Vector to Carrier; · to ×"
-}

{-
NearMonoid¹ = M-Set-Record single-sorted "Carrier"
-}

{-   700
ScalarTerm = M-Set data "Scalar"
-}

{-
M-Set-Sorts = M-Set record ⟴ sorts
-}

{-
MonoidSignature = M-Set-Record generated (λ e → (and (s-contains? "Scalar" (element-type e)) (not (s-contains? "Vector" (element-type e)))))
-}

{-
MonSig = M-Set-Record signature
-}

{-
𝒱-empty-module = :kind module :level none :waist 999
Neato = M-Set empty-module
-}

{- A module where the elements are all parameters -}
-- open Neato using ()

{-
M-Set-R = M-Set record
M-Set-R₁ = M-Set-R ⟴ open (λ x → (concat x "₁"))
-}

{-
M-Set-R-SV = M-Set-R opening "Scalar to S; Vector to V"
-}

{-
Algebra  = M-Set record
Algebra′ = Algebra open-with-decoration "′"
Hom  = Algebra hom
Hom² = Algebra hom ⟴ renaming "map₁ to scalar; pres-𝟙 to unity" :adjoin-retract nil
-}

-- _ : {Src Tgt : Algebra} → Hom² Src Tgt → Algebra.Scalar Src → Algebra.Scalar Tgt
-- _ = Hom².scalar

{-
-- regular expression test --

crazy-name-[]-+-\-^-*-? = M-Set extended-by "_+_ : Scalar; _*_ : Vector; ^ : Set; [_] : Set" :adjoin-retract nil ⟴ record

PackageFormer MagmaP : Set₁ where
  Carrier : Set
  op      : Carrier → Carrier → Carrier

Magma = MagmaP ⟴ record

Pointed   = Magma extended-by "e : let Carrier = Carrier in Carrier" ⟴ record
Additive+ = Pointed renaming "op to _+_; e to O; Carrier to C" ⟴ record
Additive× = Additive+ renaming "_+_ to _×_"

crazy-name-test  = Pointed map (λ e → (map-name (λ n → (concat n "/crazy-name-[]-+-\-^-*-?")) e)) ⟴ record
crazy-name-test2 = crazy-name-test map (λ e → (map-name (λ n → (concat n "+2")) e)) ⟴ record
-}

{-
M-Set-R′ = M-Set-R open-with-decoration "′"
-}
