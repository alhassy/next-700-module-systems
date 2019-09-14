{- (progn (load-file "PackageFormer.el") (700-mode))

(setq variationals nil)
-}

module Testing where
open import Testing_Generated
open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String hiding (_++_)

{-700
PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x
-}

{-700
PackageFormer M-Set : Set₁ where
   Scalar  : Set
   Vector  : Set
   _·_     : Scalar → Vector → Vector
   𝟙       : Scalar
   _×_     : Scalar → Scalar → Scalar
   leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋
   assoc   : ∀ {a b 𝓋} → (a × b) · 𝓋  ≡  a · (b · 𝓋)

NearRing = M-Set record ⟴ single-sorted "Scalar"
-}











-- (setq variationals nil)

-----------------------------------------------------------------------------------------

{-
𝒱-primedₗₑₜ = :alter-elements (lambda (fs) (-as-> (-unzip (--zip-with `(,other  ,(format "let %s = %s in " (get-name it) (get-name other))) fs (--map (map-name (concat name "′") it) fs))) yup (--zip-with (map-type (concat (s-join "" it) type) other) (-inits (cadr yup)) (car yup))))

MonoidR    =  MonoidP record
MonoidR′   =  MonoidP record ⟴ primedₗₑₜ
MonoidR″   =  MonoidR primedₗₑₜ

-- Operationally: Pf v₀ ⟴ ⋯ ⟴ vₙ ≈ ((Pf v₀) v₁) ⋯) vₙ
-- Note: In the concrete syntax, such parenthisation is not permitted.

-}

-- _ = MonoidR
-- _ = MonoidR′
-- _ = MonoidR″

{- 00
𝒱-map₀ elements = :alter-elements (lambda (fs) (-as-> (-unzip (--zip-with `(,other  ,(format "let %s = %s in " (get-name it) (get-name other))) fs (mapcar elements fs))) yup (--zip-with (map-type (concat (s-join "" it) type) other) (-inits (cadr yup)) (car yup))))

Monoidₘ = MonoidR map₀ :elements (lambda (f) (make-tn (concat (get-name f) "ₘ") (get-type f)))

-- Note the prime on the rhs. MA: Maybe avoid this?
𝒱-rename₀ elements = map₀ :elements 'elements

𝒱-rename₁ elements = map₀ :elements (lambda (f) (make-tn (rename-mixfix elements (get-name f)) (get-type f)))

Monoidₙ = MonoidR rename₁ :elements (lambda (name) (concat name "ₙ"))
-}

-- _ = Monoidₘ   -- Notice the name is “_⨾_ₘ”
-- _ = Monoidₙ   -- Notice the name is “_⨾ₙ_”
--               -- The differences are due to the choice of renaming scheme above.

{- lisp
(𝒱 primer = :alter-elements (lambda (es)
   (let* ((esnew es)
         ;; Let's try to accomodate for names with underscores
         (names_ (--map (element-name it) es))
         (names  (--map (s-replace "_" "" it) names_))
         (oldies (append names names_))
         (newies (--map (rename-mixfix (λ n → (concat n "′")) it) oldies)))

     (loop for old in oldies
           for new in newies
           do (setq esnew (--map (element-replace old new it) esnew)))

     ;; return value
    (message-box "%s" esnew)
     esnew)))
-}
-- Wont work for some reason.
{- 700
M-Set′-raw = M-Set primer
-}

-----------------------------------------------------------------------------------------
--- §6. Modules: Opening

{- 700
𝒱-empty-module = :kind module :level none :waist 999
Neato = M-Set empty-module
-}

-- open Neato using () -- A module where the elements are all params

{- lisp
(𝒱 open with avoid-mixfix-renaming
  =
    "Reify a given PackageFormer as a *parameterised* Agda “module” declaration.

     WITH is a renaming, string to string, function that is applied to the parent record that will
     be opened and reexported as a module.

     AVOID-MIXFIX-RENAMING is optional; by default renaming “jumps over” underscores,
     but providing a non-nil value for this argument leaves underscores alone.
     It is a matter of having, say, default “_⊕ₙ_” versus “_⊕_ₙ”.

     The resulting module has a parameter, whose name is irrelevant but is
     of the form “Arg𝒹𝒹𝒹𝒹” for some digits 𝒹 in order to minimise clash with
     any user-defined names.

     Besides the addition of a new parameter, all element qualifiers are discarded.
    "
    :kind module
    :level none
    :waist 1
    :alter-elements  (lambda (fs)
      (let ((kind "{! !}") (ℛ (format "Ar%s" (gensym))))
        (cons (make-element :name ℛ :type $𝑝𝑎𝑟𝑒𝑛𝑡)
          (--map (let ((name (if avoid-mixfix-renaming (with (element-name it)) (rename-mixfix with (element-name it)))))
            (make-element :name name
                          :type (format "let open M-Set-R %s in %s" ℛ (element-type it))
                          :equations (list (format "%s = M-Set-R.%s %s" name (element-name it) ℛ)))) fs)))))

;;

;; Notice that we do not need any “open ⋯ public” since all elements are top- level.
;; We are not making using of Agda's renaming facility.
-}

{- lisp
;; “with” should be a “;”-separated string of “to”-separated pairs; c.g. ‘𝒱-renaming’.
(𝒱 opening with
  = open :avoid-mixfix-renaming t :with '(lambda (name)
      (let (clauses)
        (thread-last with
          (s-split ";")
          (--map (s-split " to " it))
          (--map (list (s-trim (car it)) (s-trim (cadr it))))
          (-cons* 'pcase 'name)
          (setq clauses)
        )
      (eval (append clauses '((otherwise "_"))))
      ; Alternatively, we could have used ‘trash’ names:
      ; (eval (append clauses '((otherwise (format "%s" (gensym))))))
      )))))
-}

{- lisp
(𝒱 open-with decoration
  = open :with (lambda (x) (concat x decoration)))
-}

{- 700
M-Set-R = M-Set record
M-Set-R₁ = M-Set-R open :with (lambda (x) (concat x "HFFF₁"))
M-Set-R′ = M-Set-R open-with :decoration "′"
M-Set-R-SV = M-Set-R opening :with "Scalar to S; Vector to V"
-}

-- open M-Set-R₁ using ()
-- open M-Set-R′ using ()
-- open M-Set-R-SV using ()

-- _ : M-Set-R → Set
-- _ = M-Set-R′.Scalar′

-- It is important to observe that ‘openings’ are lossy:
-- They lose the types of the declarations and so cannot be used further to construct
-- new pacaking mechanisms. They are a terminal construction.

-----------------------------------------------------------------------------------------
--- §7. Sub-PackageFormers: Generated-by and Keeping

{- lisp
;; “by” is a predicate on elements.
(𝒱 generated by
  = :alter-elements  (lambda (fs)
      (let* ( (yeses (--map (funcall by it) fs))
              (get-yeses (lambda () (--filter it (--zip-with (if it other) yeses fs))))
              (in-yeses (lambda (e)
                          (--any
                           (s-contains? (s-replace "_" " " (element-name e)) (element-type it))
                           (funcall get-yeses)))))

        (loop for _ in fs do
              (loop for f in fs
                    for i from 0
                    do ;; when f in yess, set f to be yes.
                    (when (funcall in-yeses f) (setf (nth i yeses) t))))

        (funcall get-yeses))))
-}

-- Here's some nifty applications!

{- 700
𝒱-sorts = generated :by (lambda (f) (s-contains? "Set" (target (element-type f))))

M-Set-Sorts = M-Set record ⟴ sorts
-}
-- _ = M-Set-Sorts

{- 700
MonoidSignature = M-Set record ⟴ generated :by (lambda (e) (and (s-contains? "Scalar" (element-type e)) (not (s-contains? "Vector" (element-type e)))))
-}
-- _ = MonoidSignature

{- lisp
(defun targets-a-sort (element)
  (--any (s-contains? it (target (element-type element))) (-map #'element-name (-filter #'is-sort $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠))))

(𝒱 signature = generated :by (lambda (e) (targets-a-sort e)))
-}

{- 700
MonSig = M-Set record ⟴ signature
-}

-- _ = MonSig

-----------------------------------------------------------------------------------------
--- §8. Mechanising Homomorphism Formulations

{- lisp
(defun to-subscript (n)
  (nth n '("₀" "₁" "₂" "₃" "₄" "₅" "₆" "₇" "₈" "₉")))

(defun homify (element sort)
  "Given a typed name, produce the associating “preservation” formula.
   E.g.,
            _·_    : Scalar → Vector → Vector
            pres-· : {x₁ : Scalar} → {x₂ : Vector} → map₂ (x₁ · x₂) = map₁ x₁ ·′ map₂ x₂

  Type τ gets variable xᵢ provided (i, τ) ∈ sorts; likewise we think of mapᵢ : τ → τ′.
  Note that we must have i ∈ 0..9, otherwise there'll be unexpected subscripting errors.

  The target name is primed, “·′”.
 "
 (letf* ((sorts     (mapcar #'car sort))
         ((symbol-function 'index) (lambda (s) (to-subscript (cdr (assoc it sort)))))

         (tn→       (s-split " → " (element-type element)))
         (arg-count (1- (length tn→)))

         (all-indicies  (--map (index it) (--filter (member (s-trim it) sorts) tn→)))
         (indicies  (-drop-last 1 all-indicies))
         (tgt-idx   (car (-take-last 1 all-indicies)))

         (op        (element-name element))
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
 (make-element
   :name (format "pres-%s" (s-replace "_" "" (element-name element)))
   :type (s-join " → " tn→))
 )
)

;; obsolote example.
;; (homify "_·_    : Scalar → Vector → Vector" '( ("Scalar" . 4) ("Vector" . 1)))
-}

{- lisp
(𝒱 hom
  = record ⟴
    :remark "The $𝑝𝑎𝑟𝑒𝑛𝑡 and $𝑝𝑎𝑟𝑒𝑛𝑡′ should be defined as a record."
    :waist 2
    :alter-elements (lambda (es)

    (let (maps eqns sorts (𝒮𝓇𝒸 "Src") (𝒯ℊ𝓉 "Tgt"))

      ;; Construct the mapᵢ : sortᵢ → sortᵢ′; keeping track of (sort . i) pairs.
      (loop for e in es
            for i from 1
       do

         (when (is-sort e)
           (push (cons (element-name e) i) sorts)
           (push
(make-element :qualifier "field"
              :name (format "map%s" (to-subscript i))
              :type (format "%s → %s′" (element-name e) (element-name e)))
                 maps))


          (when (and (targets-a-sort e) (not (is-sort e)))
            (push (car (parse-elements (list (homify (format "%s : %s" (element-name e) (element-type e)) sorts)))) eqns)))


    ;; Ensure we have a source and target space as elements.
    (-cons*
    (make-element :qualifier "field" :name 𝒮𝓇𝒸 :type $𝑝𝑎𝑟𝑒𝑛𝑡)
    (make-element :qualifier "field" :name 𝒯ℊ𝓉 :type $𝑝𝑎𝑟𝑒𝑛𝑡)
    (--map
      (map-type (lambda (τ) (format "let open %s %s; open %s′ %s in %s" $𝑝𝑎𝑟𝑒𝑛𝑡 𝒮𝓇𝒸 $𝑝𝑎𝑟𝑒𝑛𝑡 𝒯ℊ𝓉 τ))
      (map-qualifier (lambda (_) "field") it))
    (reverse (-concat eqns maps))))
)))
-}

{- 700
Homes  = M-Set-R hom
Homes² = M-Set-R hom ⟴ renaming :by "map₁ to scalar; pres-𝟙 to unity"
-}
-- _ = Homes
-- _ = Homes²

-- _ : {Src Tgt : M-Set-R} → Homes² Src Tgt → M-Set-R.Scalar Src → M-Set-R.Scalar Tgt
-- _ = Homes².scalar
