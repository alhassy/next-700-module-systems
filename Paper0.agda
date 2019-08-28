{- (progn (load-file "prototype/PackageFormer.el")
     (700-mode) (setq 700-highlighting nil))

Find definition with M-. on the “_ = ⋯” lines to see the generated code
or simply hover your mouse over any PackageFormer's name to see the generated code.
-}

module Paper0 where
open import Paper0_Generated
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

{-700
𝒱-record = "Reify as Agda “record”." :kind record :waist-strings ("field")

Monoid₀′ = MonoidP record
Monoid₁″ = MonoidP record ⟴ :waist 1
Monoid₂″ = MonoidP record ⟴ :waist 2
-}

_ = Monoid₀′
_ = Monoid₁″
_ = Monoid₂″

--- Algebraic Data Types -------------------------------------------------------------

{-lisp
(𝒱 termtype carrier
  = "Reify as parameterless Agda “data” type.

     CARRIER refers to the sort that is designated as the
     domain of discourse of the resulting single-sorted inductive term data type.
    "
    :kind data
    :level dec
    :alter-elements (lambda (fs)
      (thread-last fs
        (--filter (s-contains? carrier (target (get-type it))))
        (--map (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) it)))))
-}

-- Commented out to avoid polluting namespace with its constructors
{-700
Monoid₃′ = MonoidP termtype :carrier "Carrier"
-}
_ = Monoid₃′

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
    termtype :carrier 'carrier   ;; Notice that passed arguments need to be quoted.
    ⟴
    :alter-elements (lambda (fs)
      (let* ((vars (format "Vars%s" (gensym)))
             (universe (format "%s %s" $𝑛𝑎𝑚𝑒 vars)))
      (-cons* (format "%s : Set" vars)
              (format "inj : %s → %s" vars universe)
       (--map (map-type (s-replace $𝑛𝑎𝑚𝑒 universe type) it) fs))))
    ⟴ :waist 1
)
-}

{-700
-- Commented out to avoid polluting namespace with its constructors
Monoid₄ = MonoidP termtype-with-variables :carrier "Carrier"
-}
_ = Monoid₄

---- PackageFormers with Equations -----------------------------------------------------------------

{-700
PackageFormer MonoidPE : Set₁ where

    -- A few declarations
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    -- assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)

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

{-lisp
(defun type-declarations-and-equations (elements)
  "Given a list of PackageFormer ‘elements’, type the elements by shape:
   Declarations are atoms, equations are lists of declarations with bindings.
   Consequently, “consp” is true for equations and false for declarations.

   The order is preserved in-case there are declarations that make use of definitions.
   "

  ;; For variety, here's a nested loop.
  (-let [es (mapcar #'list elements)]
  (loop for i from 0
        for e in es
        do
          (loop for j from 0 to (1- i)
            do
              ;; If the name of e occurs in the prefix,
              ;; then move e to the location in the prefix,
              ;; and zero-out the current location.
              (-let [name (car (s-split " " (car e)))]
                 (when
                   ;; Use an empty string in-case the location is nil.
                   (equal name (car (s-split " " (or (car (nth j es)) ""))))
                   (setf (nth j es) (append (nth j es) e))
                   (setf (nth i es) nil)))))
  (setq es (--reject (not it) es)) ;; Drop the nils.
  ;; Declarations are atoms, equations are lists of declarations with bindings.
  (--map (if (= 1 (length it)) (car it) it) es)))

;; For example:
;;
;; (type-declarations-and-equations '("A : Set" "B : Set" "C : ℕ → Set" "B = A" "C zero = A" "C (suc n) = A"))
;; ⇒ (A : Set (B : Set B = A) (C : ℕ → Set C zero = A C (suc n) = A))

(𝒱 recordₑ
  = "Record variation with support for equations."
    :kind record
    :alter-elements (lambda (es)
      (thread-last es
        type-declarations-and-equations
        (--map (if (consp it) (format "top-level %s" (s-join " ; " it)) (format "field %s" it))))))
-}

{-lisp
(𝒱 map elements = :alter-elements (lambda (fs)
   (let* ((fsnew (mapcar elements fs))
          sep
          it′
          (names  (--map (s-replace "_" "" (get-name it)) fs))
          (names′ (--map (s-replace "_" "" (get-name it)) fsnew)))
     (loop for old in names
           for new in names′
           for i from 0 to (length fs)
           do
           (setq fsnew
                 (--map
                   (progn
                     (setq sep (if (s-contains? "=" it) "=" ":"))
                     (setq it′ (s-split sep it))
                     (setf (cdr it′) (s-join sep (cdr it′)))
                     ;; If old has _ in it, then account for forms with all _ in them or none in them (which is handled by the previous clause.)
                     (setf (cdr it′) (replace-regexp-in-string (format "\\b%s\\b" (regexp-quote old)) new (cdr it′) t))
                     (when (s-contains? "_" (nth i fs))
                          (setf (cdr it′) (s-replace (get-name (nth i fs)) (get-name (funcall elements (nth i fs))) (cdr it′))))
                     (format "%s%s%s" (car it′) sep (cdr it′))) fsnew)))
     ;; return value
     fsnew
     )))

;; “elements” is a string-to-string function acting on names.
(𝒱 rename elements
  = map :elements
        (lambda (e) (-let [it (s-split " " e)] (setf (nth 0 it) (rename-mixfix elements (nth 0 it))) (s-join " " it))))

(𝒱 decorated  by  =  rename :elements (lambda (name) (concat name by)))
-}
--
-- “\\b” matches the empty string, but only at the beginning or end of a word.
-- Thus, “\\bfoo\\b” matches any occurence of “foo” as a seperate word, without any
-- prefix or suffix.
-- E.g., (replace-regexp-in-string "\\bT\\b" "NEW" "T and T₀ ∀ {and : T} but not ‵T End." t)


{-------------------------------------------------------------------------------------------}
{-      Since we're going to be defining top-level functions, such as “Lid”,               -}
{-      we will encounter “multiple definitions” errors from Agda.                         -}
{-      To avoid this, we shall decorate the resulting derivatives as we go along.         -}
{-------------------------------------------------------------------------------------------}

{-700
-- Monoid = MonoidPE map :elements         (lambda (e) (-let [it (s-split " " e)] (setf (nth 0 it) (rename-mixfix (lambda (n) (format "%s₃₃" n)) (nth 0 it))) (s-join " " it))))
-- MonoidPE₀ = MonoidPE rename :elements (lambda (n) (format "%s₀" n))
-- MonoidPE₁ = MonoidPE decorated :by "₁"

Monoid⁰ = MonoidPE decorated :by "⁰" ⟴ recordₑ
-}

-- For example: “Concatenation over an arbitrary monoid”
concat₀ : {M : Monoid⁰}
         → let C = Monoid⁰.Carrier⁰ M
           in List C → C
concat₀ {M} = Monoid⁰.concat⁰ M


{-700
-- All equations are blatantly ignored.
Monoid₆ = MonoidPE termtype :carrier "Carrier" ⟴ decorated :by "₆"
-}
_ = Monoid₆

{-lisp
(𝒱 termtypeₑ carrier
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
    :kind data
    :level dec
    :alter-elements (lambda (es)
      (let (trash)
      (thread-last es
        type-declarations-and-equations
        ;; Keep items that are either equations or target ‘carrier’; [§].
        (--separate (or (consp it) (s-contains? carrier (target (get-type it)))))
        (funcall (lambda (it) (setq trash (cdr it)) (car it)))
        ;; Change ‘carrier’ with the name of the new PackageFormer
        (--map (if (not (consp it)) (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) it) it))
        (--map (if (consp it) (cons (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) (car it)) (cdr it)) it))
        ;; Stick any equations alongside their declarations
        (--map (if (consp it) (format "sibling %s" (s-join " ; " it)) it))
        ;; Drop any items that mention non-constructors; i.e., that mention items dropped in stage [§].
        (--filter (not (some (lambda (no) (s-contains? (get-name no) it)) (car trash))))))))
-}

{-700
Monoid³ = MonoidPE decorated :by "³" ⟴ termtypeₑ :carrier "Carrier³"
-}

-- For example: “Concatenation over an arbitrary *closed* monoid term”
concat₃ : let C = Monoid³
          in List C → C
concat₃ = concat³

{-
-}
