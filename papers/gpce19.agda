{- (progn (load-file "prototype/PackageFormer.el")
     (700-mode) (setq 700-highlighting nil))

Find definition with M-. on the “_ = ⋯” lines to see the generated code
or simply hover your mouse over any PackageFormer's name to see the generated code.
-}

module gpce19 where
open import gpce19_Generated
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List hiding (concat)

{-700
PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x
-}

------ Identity variational ----------------------------------------------------------

{-700
-- Variational with empty right hand side.
𝒱-identity = "Do nothing variational"
MonoidPⁱᵈ = MonoidP identity

-- No variational clauses needed!
MonoidP⁰  = MonoidP

-- Identity of composition ⟴
MonoidPᶜ = MonoidP ⟴

-- Operationally: Pf ⟴ v  ≈  Pf v ⟴  ≈  Pf v
--                id ⟴ v  ≈ v ≈ v ⟴ id

-- “⟴” is just forwards composition:
-- We ‘thread’ the Pf through the compositions vᵢ in order.
-}

----- “record” Variational -----------------------------------------------------------

{-lisp
(𝒱 record
 = "Reify a variational as an Agda “record”.
    Elements with equations are construed as
    derivatives of fields  ---the elements
    without any equations.
   "
  :kind record
  :alter-elements
    (λ es → (--map (map-qualifier
      (λ _ → (unless (element-equations it)
               "field")) it) es)))
-}

{-700
Monoid₀′ = MonoidP record
Monoid₁″ = MonoidP record ⟴ :waist 1
Monoid₂″ = MonoidP record ⟴ :waist 2
-}

_ = Monoid₀′
_ = Monoid₁″
_ = Monoid₂″

--- Algebraic Data Types -------------------------------------------------------------

{-lisp
(𝒱 termtype carrier (discard-only-equations nil)
  = "Reify as parameterless Agda “data” type.

     CARRIER refers to the sort that is designated as the
     domain of discourse of the resulting single-sorted inductive term data type.

     Elements with equations are simply ignored altogether,
     unless optional argument DISCARD-ONLY-EQUATIONS is non-nil.
    "
    :kind data
    :level dec
    :alter-elements (lambda (es)
      (thread-last
        (if discard-only-equations
          (--map (map-equations (λ _ → nil) it) es)
         (--filter (not (element-equations it)) es))
        (--filter (s-contains? carrier (target (element-type it))))
        (--map (map-type (λ τ → (s-replace carrier $𝑛𝑎𝑚𝑒 τ)) it)))))
-}

-- Commented out to avoid polluting namespace with its constructors
{-   700
Monoid₃′ = MonoidP termtype "Carrier"
-}
-- _ = Monoid₃′

-- Note: This is the first occurance  of “termtype” in Paper0.
-- Below is the second occurance.

{-lisp
(𝒱 termtype-with-variables carrier
  =
    "Reify a given PackageFormer as a *parameterised* Agda “data” declaration.

     CARRIER refers to the sort that is designated as the
     domain of discourse of the resulting single-sorted inductive term data type.

     The resulting data type has a parameter, whose name is irrelevant but is
     of the form “Varsg𝒹𝒹𝒹𝒹” for some digits 𝒹 in order to minimise clash with
     any user-defined names.

     For brevity, the resulting embedding of the variables into the term type
     is called “inj”. The user must ensure there is no name clash, and may rename
     it easily using the rename variational.
    "
    termtype 'carrier   ;; Notice that passed arguments need to be quoted.
    ⟴
    :alter-elements (lambda (fs)
      (let* ((vars (format "Vars%s" (gensym)))
             (universe (format "%s %s" $𝑛𝑎𝑚𝑒 vars)))
      (-cons* (make-element :name vars :type "Set")
              (make-element :name "inj" :type (format "%s → %s" vars universe))
       (--map (map-type (lambda (τ) (s-replace $𝑛𝑎𝑚𝑒 universe τ)) it) fs))))
    ⟴ :waist 1
)
-}

{-   700
-- Commented out to avoid polluting namespace with its constructors
Monoid₄ = MonoidP termtype-with-variables "Carrier"
-}
-- _ = Monoid₄

---- PackageFormers with Equations -----------------------------------------------------------------

{-700
PackageFormer MonoidPE : Set₁ where

    -- A few declarations
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

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
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → Rid x ≡ x

    -- Since there are no more pure declarations, “fields”, subsequent equations
    -- may use pattern matching.

    Id² : Id ⨾ Id ≡ Id
    Id² = rightId

    concatₚ : List Carrier → Carrier
    concatₚ []       = Id
    concatₚ (x ∷ xs) = x ⨾ concatₚ xs

-- Notice that there is no particular segregation of declarations and equations.
-- Simply: A declaration may /optionally/ have an associated equation; however
-- once an equation uses pattern matching then all subsequent declarations must also
-- have equations ─this is a constraint of the current Agda implementation.
-}

{--------------------------------------------------------------------------------------------}
{-      Since we're going to be defining top-level functions, such as “Lid”,                -}
{-      we will encounter “multiple definitions” errors from Agda.                          -}
{-      To avoid this, we shall decorate the resulting derivatives as we go along.          -}
{-                                                                                          -}
{-      Variationals map, rename, decorated are useful enough to be shipped with the system -}
{--------------------------------------------------------------------------------------------}

{-700
Monoid-woah = MonoidPE termtype "Carrier" :discard-only-equations t

-- Monoid⁰ = MonoidPE decorated "⁰" ⟴ record
-- Monoid³ = MonoidPE decorated "³" ⟴ termtype "Carrier³"
-}

-- For example: “Concatenation over an arbitrary monoid”
-- concat₀ : {M : Monoid⁰}
--          → let C = Monoid⁰.Carrier⁰ M
--            in List C → C
-- concat₀ {M} = Monoid⁰.concat⁰ M

-- Notice that we have the option to blatantly ignore all equational names,
-- or only to discard their equations. Yet another route is to lift the equational names
-- as derived operations.

-- For example: “Concatenation over an arbitrary *closed* monoid term”
-- concat₃ : let C = Monoid³
--           in List C → C
-- concat₃ = concat³
