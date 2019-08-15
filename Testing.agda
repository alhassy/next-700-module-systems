{- (load-file "PackageFormer.el") -}

{-
0. There are a number of common use-cases.
1. We can handle all of them & more, since we're extensible.
  - Mention the Lean & Coq, as well as the Agda, repeated fragments.
2. The resulting setup is pragmatic: It is unobtrusive in the
   traditional Agda coding style in that it happens in the background.
3. It fills a particular need; the desire to avoid repetitious code.
-}

-----------------------------------------------------------------------------------------

-- The space causes this block to be treated as a normal comment block.
-- Having no space between “{-” and “lisp” would cause the block to be executed
-- as a single Lisp form.
{-  lisp
(progn (message-box "Hello")
(message-box "World"))
-}

{- lisp
(message-box "Friend")
-}


module Testing where
open import Testing_Generated

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)

------------------------------------------------------------------------------------------
--- §0. Basic PackageFormer declarations

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

-- Gives error that 𝒱-doit is not defined (งಠ_ಠ)ง
-- Whoops   =  MonoidP doit
-}

-----------------------------------------------------------------------------------------
---- §1. Empty Variationals

{- Find definition with M-. on the “_ = ⋯” lines to see the generated code -}

{-700
-- Variational with empty right hand side.
𝒱-identity =
MonoidPⁱᵈ = MonoidP identity

-- No variational clauses needed!
MonoidP⁰  = MonoidP

-- Identity of composition ⟴
MonoidPᶜ = MonoidP ⟴

-- Operationally: Pf ⟴ v  ≈  Pf v ⟴  ≈  Pf v

-- “⟴” is just forwards composition: We ‘thread’ the Pf through the compositions vᵢ in order.

-}

-----------------------------------------------------------------------------------------
----- §2. Record-based Variationals

{-700
-- 𝒱-whoops              = :type recorder :waist-strings ("field")

𝒱-record                 = :type record :waist-strings ("field")
𝒱-typeclass-attempt      = :type record :waist-strings ("field") :waist 2
𝒱-typeclass₂             = :type record :waist-strings ("field") :waist 2 :level dec
𝒱-typeclass height level = record ⟴ :waist height :level level

MonoidT₃   =  MonoidP record ⟴ :waist 3 :level dec
MonoidT₂   =  MonoidP typeclass₂ ⟴ :waist-strings ("private" "extra : Set₁" "extra = Set" "field")
MonoidT₄   =  MonoidP typeclass :height 4 :level 'dec
-}

{-700
M-Set-Record = M-Set record
M-Set-Typeclass₃ = M-Set-Record typeclass :height 3 :level 'dec
-}

_ = MonoidT₃
_ = MonoidT₂
_ = MonoidT₄
_ = M-Set-Record
_ = M-Set-Typeclass₃

-----------------------------------------------------------------------------------------
----- §3. Variationals via Lisp: Primed, map-elements, renaming
-----     ( Feel free to skip this and look at §4 for a better way to do things. )

{-700

-- First one is intensionally erroenous attempt.
𝒱-primed-attempt = :alter-elements (lambda (fs) (mapcar (lambda (f) (map-name (concat name "′") f)) fs))

𝒱-primedₗₑₜ = :alter-elements (lambda (fs) (-as-> (-unzip (--zip-with `(,other  ,(format "let %s = %s in " (get-name it) (get-name other))) fs (--map (map-name (concat name "′") it) fs))) yup (--zip-with (map-type (concat (s-join "" it) type) other) (-inits (cadr yup)) (car yup))))

-- M-Set′-attempt = M-Set record ⟴ primed-attempt

MonoidR    =  MonoidP record
MonoidR′   =  MonoidP record ⟴ primedₗₑₜ
MonoidR″   =  MonoidR primedₗₑₜ

-- Operationally: Pf v₀ ⟴ ⋯ ⟴ vₙ ≈ ((Pf v₀) v₁) ⋯) vₙ
-- Note: In the concrete syntax, such parenthisation is not permitted.

-}

_ = MonoidR
_ = MonoidR′
_ = MonoidR″

{-700
𝒱-map₀ elements = :alter-elements (lambda (fs) (-as-> (-unzip (--zip-with `(,other  ,(format "let %s = %s in " (get-name it) (get-name other))) fs (mapcar elements fs))) yup (--zip-with (map-type (concat (s-join "" it) type) other) (-inits (cadr yup)) (car yup))))

Monoidₘ = MonoidR map₀ :elements (lambda (f) (make-tn (concat (get-name f) "ₘ") (get-type f)))

-- Note the prime on the rhs. MA: Maybe avoid this?
𝒱-rename₀ elements = map₀ :elements 'elements

𝒱-rename₁ elements = map₀ :elements (lambda (f) (make-tn (rename-mixfix elements (get-name f)) (get-type f)))

Monoidₙ = MonoidR rename₁ :elements (lambda (name) (concat name "ₙ"))
-}

_ = Monoidₘ   -- Notice the name is “_⨾_ₘ”
_ = Monoidₙ   -- Notice the name is “_⨾ₙ_”
              -- The differences are due to the choice of renaming scheme above.

-----------------------------------------------------------------------------------------
--- §4. Variationals via Lisp, Continue: Primed, map-elements, renaming
--      Using lisp-blocks and without let-in clauses.

{-lisp
(𝒱 primer = :alter-elements (lambda (fs)
   (let ((fsnew fs)
         (names (--map (s-replace "_" "" (get-name it)) fs)))
     (loop for old in names
           for new in (--map (concat it "′") names)
           do
           ;; (message-box "old %s; new %s" old new)
           (setq fsnew (--map (s-replace old new it) fsnew)))
     ;; return value
     fsnew
     )))
-}

{-700
MR′ = M-Set record ⟴ primer
-}
_ = MR′

{-lisp
;; Underscores are not given any special consideration.
(𝒱 map_ elements = :alter-elements (lambda (fs)
   (let* ((fsnew (mapcar elements fs))
          (names  (--map (get-name it) fs))
          (names′ (--map (get-name it) fsnew)))
     (loop for old in names
           for new in names′
           do
           (setq fsnew (--map (map-type (s-replace old new type) it) fsnew)))
     ;; return value
     fsnew
     )))

(𝒱 map elements = :alter-elements (lambda (fs)
   (let* ((fsnew (mapcar elements fs))
          (names  (--map (s-replace "_" "" (get-name it)) fs))
          (names′ (--map (s-replace "_" "" (get-name it)) fsnew)))
     (loop for old in names
           for new in names′
           do
           (setq fsnew (--map (map-type (s-replace old new type) it) fsnew)))
     ;; return value
     fsnew
     )))
-}
--
-- Note that we cannot form a “map_” that does not rewrite “_” with “”
-- and expect it to work as desired. Indeed, if we have a name, say, “_⊕_”
-- but one of its uses is “x ⊕ y” then any alteration would not transpire
-- since “x ⊕ y” clearly does not mention the literal “_⊕_”.
-- Agda let's use use opertor names in prefix and mixfix, as such our schemes
-- need to be more robust ---which the reader may pursue with sufficint Lisp.
--
-- We only show this briefly with rename_ and renaming_ below.

-- Now for some useful corollaries.

{-lisp

;; “elements” is a string-to-string function acting on names.
(𝒱 rename elements
  = map :elements
     (lambda (f) (make-tn (rename-mixfix elements (get-name f)) (get-type f))))


;; “elements” is a string-to-string function acting on names.
;; Underscores are not given any special consideration.
(𝒱 rename_ elements
  = map :elements
     (lambda (f) (make-tn (funcall elements (get-name f)) (get-type f))))

(𝒱 decorated    by  =  rename :elements (lambda (name) (concat name by)))

(𝒱 co-decorated by  =  rename :elements (lambda (name) (concat by name)))
-}

{-700
MR₁₋₂    = M-Set record ⟴ decorated :by "₁" ⟴ decorated :by "₂"
the-MR   = M-Set record ⟴ co-decorated :by "the-"
-}
_ = MR₁₋₂
_ = the-MR

-----------------------------------------------------------------------------------------
--- §5. Renaming with “to” lists

{-700
MR-oh  = M-Set record ⟴ rename :elements (lambda (name) (pcase name ("Scalar" "S") (x x)))
-}
_ = MR-oh

{-lisp
;; “by” should be a “;”-seperated string of “to”-seperated pairs.
(𝒱 renaming by
  = rename :elements '(lambda (name)
      (let (clauses)
        (thread-last by
          (s-split ";")
          (--map (s-split " to " it))
          (--map (list (s-trim (car it)) (s-trim (cadr it))))
          (-cons* 'pcase 'name)
          (setq clauses)
        )
      (eval (append clauses '((otherwise otherwise))))
      )
))

;; “by” should be a “;”-seperated string of “to”-seperated pairs.
(𝒱 renaming_ by
  = rename_ :elements '(lambda (name)
      (let (clauses)
        (thread-last by
          (s-split ";")
          (--map (s-split " to " it))
          (--map (list (s-trim (car it)) (s-trim (cadr it))))
          (-cons* 'pcase 'name)
          (setq clauses)
        )
      (eval (append clauses '((otherwise otherwise))))
      )
))
-}

{-700
MRₜₒ = M-Set record ⟴ renaming :by "Scalar to S; Vector to V; · to nice"
MRₜₒ_ = M-Set record ⟴ renaming_ :by "Scalar to S; Vector to V; _·_ to _nice_"
NearMonoid = M-Set record ⟴ renaming :by "Scalar to Carrier; Vector to Carrier; · to ×"
-}

_ = MRₜₒ
_ = MRₜₒ_

-- As the underscore variant shows, one must ensure that the new names either are the same
-- fixity or are in prefix form in the PackageFormer being instantiated.

_ = NearMonoid

-- Notice that this example demonstrates multiplicity of PackageFormer elements is irrelevant.
-- That is, elements are algebraically a list with the axiom xs ++ ys ++ xs  ≈  xs ++ ys.

{-lisp

(defun is-sort (element) (s-contains? "Set" (target element)))

(𝒱 single-sorted with-sort
  = map :elements (lambda (e)
      (if (is-sort e) (map-name with-sort e) e)))

-}

{-700
NearMonoid¹ = M-Set record ⟴ single-sorted :with-sort "Carrier"
-}

_ = NearMonoid¹

-----------------------------------------------------------------------------------------
--- §6. Modules: Opening

{-700
𝒱-empty-module = :type module :level none :waist 999
Neato = M-Set empty-module
-}

open Neato using () -- A module where the elements are all params

{-lisp
;; “with” is a renaming string-to-string function.
(𝒱 open with
  = :type module
    :level none
    :waist 1
    :waist-strings ("")
    :alter-elements  (lambda (fs)
      (let ((kind "{! !}"))
        (thread-last
           (--map (format "%s to %s" (get-name it) (rename-mixfix with (get-name it))) fs)
           ;; Resulting elements must be a list, so we make a singleton list.
           (s-join "\n       ; ")
           (format "    ( %s\n       )")
           list

           ;; Stick on the renaming, which in turn requires an opening clause;
           ;; which in turn requires a module parameter.
           (cons "  renaming")
           (cons (format "open %s ℛ public" $𝑝𝑎𝑟𝑒𝑛𝑡))
           (cons (format "ℛ : %s" $𝑝𝑎𝑟𝑒𝑛𝑡)))))
)

;; “with” should be a “;”-seperated string of “to”-seperated pairs; c.g. ‘𝒱-renaming’.
(𝒱 opening with
  = open :with '(lambda (name)
      (let (clauses)
        (thread-last with
          (s-split ";")
          (--map (s-split " to " it))
          (--map (list (s-trim (car it)) (s-trim (cadr it))))
          (-cons* 'pcase 'name)
          (setq clauses)
        )
      (eval (append clauses '((otherwise otherwise))))
      )
))

(𝒱 open-with decoration
  = open :with (lambda (x) (concat x decoration)))
-}

{-700
M-Set-R = M-Set record
M-Set-R₁ = M-Set-R open :with (lambda (x) (concat x "₁"))
M-Set-R′ = M-Set-R open-with :decoration "′"
-}

open M-Set-R₁ using ()
open M-Set-R′ using ()

-- It is important to observe that ‘openings’ are lossy:
-- They lose the types of the declarations and so cannot be used further to construct
-- new pacaking mechanisms. They are a terminal construction.

-----------------------------------------------------------------------------------------
--- §7. Sub-PackageFormers: Generated-by and Keeping

{-lisp
;; “by” is a predicate on elements.
(𝒱 generated by
  = :alter-elements  (lambda (fs)
      (let* ( (yeses (--map (funcall by it) fs))
              (get-yeses (lambda () (--filter it (--zip-with (if it other) yeses fs))))
              (in-yeses (lambda (e)
                          (--any
                           (s-contains? (s-replace "_" " " (get-name e)) (get-type it))
                           (funcall get-yeses)))))

        (loop for _ in fs do
              (loop for f in fs
                    for i from 0
                    do ;; when f in yess, set f to be yes.
                    (when (funcall in-yeses f) (setf (nth i yeses) t))))

        (funcall get-yeses))))
-}

-- Here's some nifty applications!

{-700
𝒱-sorts = generated :by (lambda (f) (s-contains? "Set" (target (get-type f))))

M-Set-Sorts = M-Set record ⟴ sorts
-}
_ = M-Set-Sorts

{-700
MonoidSignature = M-Set record ⟴ generated :by (lambda (f) (and (s-contains? "Scalar" f) (not (s-contains? "Vector" f))))
-}
_ = MonoidSignature

{-lisp
(defun targets-a-sort (element)
  (--any (s-contains? it (target element)) (-map #'get-name (-filter #'is-sort $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠))))

(𝒱 signature = generated :by (lambda (f) (targets-a-sort f)))
-}

{-700
MonSig = M-Set record ⟴ signature
-}

_ = MonSig

-- Compare this with “renaming” from above.
--
{-lisp
;; “those” should be a “;”-seperated string of names
(𝒱 keeping those
  = generated :by '(lambda (element)
      (let (clauses)
        (thread-last by
          (s-split ";")
          (--map (cons (s-trim it) t)) ;; t ≈ true
          (-cons* 'pcase '(get-name element))
          (setq clauses)
        )
      (eval (append clauses '((otherwise nil)))) ;; nil ≈ false
      )
))
-}

-- TODO: FIXME: !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
{- 00
𝟙-et-al = M-Set record ⟴ keeping :those "𝟙; _×_"
-}

-- _ = 𝟙-et-al

-----------------------------------------------------------------------------------------
--- §8. Mechanising Homomorphism Formulations

{-lisp
(defun homify (typed-name sort)
  "Given a typed name, produce the associating “preservation” formula.
   E.g.,
            _·_    : Scalar → Vector → Vector
            pres-· : {x₁ : Scalar} → {x₂ : Vector} → map₂ (x₁ · x₂) = map₁ x₁ ·′ map₂ x₂

  Type τ gets variable xᵢ provided (i, τ) ∈ sorts; likewise we think of mapᵢ : τ → τ′.
  Note that we must have i ∈ 0..9, otherwise there'll be unexpected subscripting errors.

  The target name is primed, “·′”.
 "
 (letf* ((sorts     (mapcar #'car sort))
         ((symbol-function 'to-subscript) (lambda (n) (nth n '("₀" "₁" "₂" "₃" "₄" "₅" "₆" "₇" "₈" "₉"))))
         ((symbol-function 'index) (lambda (s) (to-subscript (cdr (assoc it sort)))))

         (tn→       (s-split " → " (get-type typed-name)))
         (arg-count (1- (length tn→)))

         (all-indicies  (--map (index it) (--filter (member (s-trim it) sorts) tn→)))
         (indicies  (-drop-last 1 all-indicies))
         (tgt-idx   (car (-take-last 1 all-indicies)))

         (op        (get-name typed-name))
         (args      (--map (concat "x" it) indicies))
         (lhs       (format "map%s (%s %s)" tgt-idx op (s-join " " args)))

         (op′       (rename-mixfix (lambda (n) (concat n "′")) op))
         (map-args  (--map (format "(map%s x%s)" it it) indicies))
         (rhs       (format "%s %s" op′ (s-join " " map-args)))

         (target    (format "  %s   ≡   %s" lhs rhs))
 )

 ;; Change the target type.
 (setq tn→ (--map (when (assoc it sort) (format "{x%s : %s}" (index it) it)) tn→))
 (setf (nth arg-count tn→) target)

 ;; Stick it all together, with an updated name.
 (make-tn
   (format "pres-%s" (s-replace "_" "" (get-name typed-name)))
   (s-join " → " tn→))
 )
)
(homify "_·_    : Scalar → Vector → Vector" '( ("Scalar" . 4) ("Vector" . 1)))

(𝒱 hom
  = record ⟴
    :remark "The $𝑝𝑎𝑟𝑒𝑛𝑡 should be defined as a record."
    :waist 2
    :waist-strings ((format "open %s  Src" $𝑝𝑎𝑟𝑒𝑛𝑡)
                    (format "open %s′ Tgt" $𝑝𝑎𝑟𝑒𝑛𝑡)
                    "field")
    :alter-elements (lambda (es)

    (let (maps eqns sorts)

      ;; Construct the mapᵢ : sortᵢ → sortᵢ′; keeping track of (sort . i) pairs.
      (loop for e in es
            for i from 1
       do

         (when (is-sort e)
           (push (cons (get-name e) i) sorts)
           (push (format "map%s : %s → %s′" (to-subscript i) (get-name e) (get-name e))
                 maps))

          (when (and (targets-a-sort e) (not (is-sort e)))
            (push (homify e sorts) eqns)))

    ;; Ensure we have a source and target space as elements.
    (-cons* "Src : M-Set-R"
            "Tgt : M-Set-R"
    (reverse (-concat eqns maps)))
)))
-}

{-700
Hom  = M-Set-R hom
Hom² = M-Set-R hom ⟴ renaming :by "map₁ to scalar; pres-𝟙 to unity"
-}
_ = Hom
_ = Hom²

-- Here's some cuteness. ;; need to fix porting to happen in-place rather than at the top.

-- Desired:
{- 00
variable
  Src Tgt : M-Set-R

-- this comment should be ignored; why is it being ported!?
-}

{-
-- PackageFormer place-holder-so-next-line-doesnt-get-ported : Set where

Remember that ‘opening’ is a lossy operation; it is terminal and so
something like
“Hom-D = Hom opening :with "map₁ to _D₀_" ⟴ :waist 3”
has no meaning. We cannot lift ‘fields’ to ‘parameters’ since an “opening”
has lost the necessary type information for the elements.

If we want something to be parametersied; we will use Agda's generalised variables mechanism. (For now).
-}

-- _ = Hom-$

{- works

variable
  A B : M-Set-R

module Hom-D (ℛ : Hom A B) where
  ⋯
-}

-----------------------------------------------------------------------------------------
--- §9. Algebraic Data Types

{-lisp
(𝒱 data carrier
  = :type data
    :level dec
    :alter-elements (lambda (fs)
      (thread-last fs
        (--filter (s-contains? carrier (target (get-type it))))
        (--map (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) it))))
)
-}

{-00
ScalarSyntax  = M-Set primer ⟴ data :carrier "Scalar′"
ScalarTerm    = M-Set data :carrier "Scalar" ⟴ primer

-- Example of erroenous invocations.
-- Crashes since type No′ is not defined!
-- No = M-Set primer ⟴ data :carrier "Scalar"

-}
-- _ = ScalarSyntax
-- _ = ScalarTerm

-- TODO:
-- What about syntax of vectors? Well that depends on scalars!

{-lisp
(𝒱 data-with-params carrier
  = :type data
    :level dec
    :alter-elements (lambda (fs)
      (thread-last fs
        (--filter (s-contains? carrier (target (get-type it))))
        (--map (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) it))))
)
-}

-- “data with params”
-- VectorSyntax  = M-Set data :carrier "Vector" ⟴ primer

------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
-- Experiments follow --

{-
-- 𝒱-data-with-identified carrier = :type data :level dec :alter-elements (lambda (fs) (thread-last fs (--filter (-any? (lambda (c) (s-contains? c (target (get-type it)))) carrier)) (loop for c in carrier do (--map (map-type (s-replace c $𝑛𝑎𝑚𝑒 type) it)) )))

𝒱-data-with-identified carrier = :alter-functions (lambda (f) (message-box "HELLO"))

M-Set′ = M-Set record ⟴ primed

M-Set-Syntax = M-Set′ data-with-identified :carrier (list '(list "Scalar"))
-}


{-00

𝒱-data-with carrier      = map :elements (lambda (f) (when (s-contains? carrier (target (get-type f))) (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) f)))

MonoidD   =  MonoidP data-with :carrier "Carrier"

-}

{- TODO
PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier

    left-⨾  : Carrier → Carrier → Carrier → Carrier
    left-⨾ x y z = (x ⨾ y) ⨾ z

    assoc   : ∀ {x y z} → left-⨾ x y z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x

- record ⇒ local intersped with fields
- data  ⇒ rewrite [syntax sugar] and possibly global operation afterwards as an additional new method, and possibly adding it in as a constructor to the data-type, eg. See Isabelle's distinctions of definition vs abbrevation where the former rewuires an explicit tactic to apply as in coq's intro and the latter is definitional.
- module ⇒ local let, or possibly rewrite with local declaration inside module

-- MonoidR   =  MonoidP :type record :waist 2 :level dec ⟴ :waist-strings ("private" "n : Set₁" "n = Set" "field")
-- MonoidD = data-with :carrier Carrier
-}

{-
𝒱-record⁷             = :type record :waist-strings (when (package-former-elements self) '("field"))

𝒱-data-with carrier      = :type data :level dec :alter-elements (lambda (f) (if (s-contains? carrier (target (get-type f))) (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) f) ""))

𝒱-filter-attempt by = map :elements (lambda (f) (if (funcall by f) f ""))
MonoidF   = MonoidP filter :by (lambda (f) nil)

-- TODO: 7 crashes things --yikes! This is because agda keyword field cannot occur barren --c.f. 𝓥-record⁷.
-- MonoidT⁷ = MonoidP record ⟴ :waist 4
-}

------------------------------------------------------------------------------------------
-- Observations

{-00
-- MA: TODO: Useful example to know how to do. Maybe fix this whole quotation issue!
𝒱-try this = decorated :by '(car this)
Ni = M-Set record ⟴ try :this '(list "ᵢ" "ⱼ" "ₖ")

-}
-- _ = Ni

-- Passed functions need the quote.
-- E.g.,
-- 𝒱-keeping those = generated :by 'those
