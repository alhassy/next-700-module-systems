;; [[file:~/thesis-proposal/PackageFormer.org::*Finding%20Children%20in%20the%20Wild][Finding Children in the Wild:3]]
(defun get-indentation (string)
  "How many spaces are there at the front of ‘string’?

  Property: The resulting number is ‘≤ length string’.
  "
  (if string (length (s-shared-start string (s-repeat (length string) " "))) 0)
)
;; Finding Children in the Wild:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Finding%20Children%20in%20the%20Wild][Finding Children in the Wild:4]]
(cl-defun get-children (parent the-wild &key (then #'identity))
  "Go into ‘the-wild’ seeking out the first occurence of ‘parent’,
   who once found, ought to have a minimal indentation for its children.

   “Minimal” in that if there are items with a greater indentation,
    then they are children of children and should be kept.

   The first input argument is of type ‘string’,
   the second argument may be of type ‘string’ or ‘list’ of strings
   ---if it's a string, we split along new lines---,
   the optional ‘then’ is a function acting on children strings.

   Result is the parent followed by its children, as a list of lines,
   where each child has been altered using the optional ‘then’ function.
   Moreover, we also return the rest of the unconsidered portion of ‘the-wild’:

   Result list: (  unconsidered-prefix-of-the-wild
		   (cons parent-line children-lines)
		   unconsidered-remaining-lines )

   The first element is the porition that does not contain an occurence
   of ‘parent’. The second is the parent and its children, if possible.
   The third is the remainder of the wild.

   Implementation: Look at the indentation of the
   first child, then use that as a lower bound to find the indentation
   of the remaining children.
  "

  (let ((lines (if (stringp the-wild) (s-lines the-wild) the-wild))
	(indentation -1)
	prefix
	parent-line)

    ;; Ensure: lines ≈ (cons (not-here-prefix) (cons parent-here more-lines) )
    (setq lines (--split-with (not (s-contains? parent it)) lines))

    ;; Discard prefix, for now.
    (setq prefix (car lines))
    (setq lines (cadr lines))

    ;; Discard parent, but remember its contextual line.
    (setq parent-line (car lines))
    (setq lines (cdr lines))

    ;; How far is the first child indented?
    (setq indentation (get-indentation (car lines)))

    ;; Keep only the children that have at least this level of indentation.
    (setq lines&more (--split-with (<= indentation (get-indentation it)) lines))
    (setq lines (car lines&more))
    (setq unconsidered (cadr lines&more))

    ;; Alter the children according to the given function.
    (setq lines (mapcar then lines))

    ;; Yield the parent line along with the children lines; and the unconsumed wild's prefix and suffix.
    `(,prefix ,(cons parent-line lines) ,unconsidered)
  )
)
;; Finding Children in the Wild:4 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Finding%20Children%20in%20the%20Wild][Finding Children in the Wild:13]]
(ert-deftest get-ind ()
  (loop for s in '(nil "" "x" "  x" "  x ")
    do (should (<= (get-indentation s) (length s))))
  )

(ert-deftest get-child ()
  (-let [eh
"+ item 1
  - subitem 1.1
    * subsubitem 1.1.1
  - subitem 1.2
+ item 2
  - subitem 2.2
+ item 3"]

    ;; Consider each line above as a parent, with ‘eh’ as the wild.
    (loop for parent in (s-split "\n" eh) do
      (let* ((cs (get-children parent eh))
	     (children (cdadr cs)))

      ;; Result is a list of lists: Each is either nil or a cons.
      (loop for r in cs do (should (listp r)))

      ;; The parent line contains the parent.
      (should (equal parent (caadr cs)))

      ;; The children all have the same indentation.
      (loop for c in children for d in children do (should (equal (get-indentation c) (get-indentation d))))

      ;; Extensionality: Orginal input can be regained from resulting parts.
      (should (equal eh (s-trim (s-join "\n" (--map (s-join "\n" it) cs)))))
    )
  )
))
;; Finding Children in the Wild:13 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:1]]
(cl-defun substring-delimited
    (prefix suffix string)
  "Assuming ‘string’ ≈ ⋯‘prefix’⟪needle⟫‘suffix’⋯, return the /first/ such needle.

    NOTE: Delimiters ‘prefix’ and ‘suffix’ may be empty.

  We convert all adjacent whitespace
  characters to a single space in the input ‘string’ and trim any surrounding
  whitespace from the resulting output needle string.
  "

  (unless (stringp string) (error "substring-delimited: Argument ‘string’ must be a string."))
  (let* ((new (s-collapse-whitespace string)))

  (when (not (s-blank? prefix))
    (setq new (car (-take-last (if (equal prefix suffix) 2 1) (s-split prefix new)))))

  (when (not (s-blank? suffix))
    (setq new (car (s-split suffix new))))

  (s-trim new)
  ))
;; Substrings Delimited by Tokens:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:2]]
(ert-deftest subst-delimit ()
  (-let [str "𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟜 𝟞"] ;; Intentionally repeated ‘𝟜’.
    ;; Pattern for loop: (prefix postfix expected-needle :comment))
    (loop for it in `( ( "" "" ,str            :Identity)
		       ( "𝟘" "𝟞" "𝟙 𝟚 𝟛 𝟜 𝟝 𝟜"  :Boundaries)
		       ( "" "𝟞" "𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟜" :NoLeft)
		       ( "𝟘" "" "𝟙 𝟚 𝟛 𝟜 𝟝 𝟜 𝟞" :NoRight)
		       ( "𝟠" ""  ,str          :BogusL)
		       ( "" "∞"  ,str          :BogusR)
		       ( "𝟠" "∞" ,str          :BogusLR)
		     )
      do (should (equal (third it) (substring-delimited (first it) (second it) str))))

    (should (equal "𝟛" (substring-delimited "𝟚" "𝟜" str)))

    ;; Identical boundaries.
    (should (equal "𝟙" (substring-delimited "𝑳" "𝑳" "𝑳 𝟙 𝑳")))
    (should (equal ""  (substring-delimited "𝑳" "𝑳" "𝑳 𝑳")))
    (should (equal ""  (substring-delimited "𝑳" "𝑳" "𝑳𝑳")))

    ;; Multiple occurances of prefix or postfix
    (should (equal "y"  (substring-delimited "𝑳" "𝑹" "𝑳 x 𝑳 y 𝑹")))
    (should (equal "x"  (substring-delimited "𝑳" "𝑹" "𝑳 x 𝑹 y 𝑹")))
    ))
;; Substrings Delimited by Tokens:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:3]]
(cl-defun substring-delimited-$
    (context string &key preserve-spaces longest-substring)
  "Assuming ‘context’ = “⟪prefix⟫ $here ⟪suffix⟫”
   and ‘string’ ≈ ⋯‘prefix’⟪needle⟫‘suffix’⋯, return the /first/ such needle
   by default, unless ‘longest-substring’ is true, in which case yield /longest/
   such needle.

  NOTE: ⟪prefix⟫ and ⟪suffix⟫ cannot be emptry strings!

  Unless ‘preserve-spaces’ is true, we convert all adjacent whitespace
  characters to a single space in the input ‘string’ and trim any surrounding
  whitespace from the resulting output needle string.
  "

  (-let [pre-post (s-split "$here" context)]
    (substring-delimited (s-trim (car pre-post)) (s-trim (cadr pre-post)) string)
  )
)

(ert-deftest subst-delimit-$ ()
  (-let [str "𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟜 𝟞"] ;; Intentionally repeated ‘𝟜’.
    ;; Pattern for loop: (prefix postfix expected-needle :comment)
    (loop for it in `( ( "$here" ,str              :Identity)
		       ( "𝟘 $here 𝟞" "𝟙 𝟚 𝟛 𝟜 𝟝 𝟜"  :Boundaries)
		       ( "$here 𝟞" "𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟜"  :NoLeft)
		       ( "𝟘 $here"  "𝟙 𝟚 𝟛 𝟜 𝟝 𝟜 𝟞" :NoRight)
		       ( "𝟠 $here"   ,str          :BogusL)
		       ( "$here ∞"   ,str          :BogusR)
		       ( "𝟠 $here ∞" ,str          :BogusLR)
		     )
      do (should (equal (second it) (substring-delimited-$ (first it) str))))

    ;; Longest substring
    (should (equal "𝟛" (substring-delimited-$ "𝟚 $here 𝟜" str)))

    ;; Identical boundaries.
    (should (equal "𝟙" (substring-delimited-$ "𝟘 $here 𝟘" "𝟘 𝟙 𝟘")))
    (should (equal ""  (substring-delimited-$ "𝟘 $here 𝟘" "𝟘 𝟘")))
    (should (equal ""  (substring-delimited-$ "𝟘 $here 𝟘" "𝟘𝟘")))

    ;; Multiple occurances of prefix or postfix
    (should (equal "y"  (substring-delimited-$ "𝑳 $here 𝑹" "𝑳 x 𝑳 y 𝑹")))
    (should (equal "x"  (substring-delimited-$ "𝑳 $here 𝑹" "𝑳 x 𝑹 y 𝑹")))

    ;; Space irrelevance for keyword ‘$here’:
    (should (equal "𝟙" (substring-delimited-$ "𝑳 $here 𝑹" "𝑳 𝟙 𝑹")))
    (should (equal "𝟙" (substring-delimited-$ "𝑳 $here𝑹" "𝑳 𝟙 𝑹")))
    (should (equal "𝟙" (substring-delimited-$ "𝑳$here 𝑹" "𝑳 𝟙 𝑹")))
    (should (equal "𝟙" (substring-delimited-$ "𝑳$here𝑹" "𝑳 𝟙 𝑹")))
    (should (equal "𝟙" (substring-delimited-$ "𝑳      $here  𝑹" "𝑳 𝟙 𝑹")))
    ))
;; Substrings Delimited by Tokens:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:5]]
(cl-defun buffer-substring-delimited (start end &optional (highlight nil))
  "
  Get the current buffer's /next/ available substring that is delimited
  between the regexp tokens ‘start’ up to ‘end’, exclusively.

  If no tokens are found, an error is thrown.

  The ‘highlight’ option simply highlights the selected region ---visual feedback
  for the user.
  "
  (let (p1 p2)
    (re-search-forward start)
    (setq p1 (point))

    (re-search-forward end)
    (backward-word)
    (setq p2 (point))

    (when highlight ;; do we want to highlight the region?
      (goto-char p1)
      (push-mark p2)
      (setq mark-active t)
    )

    ;; (copy-region-as-kill p1 p2)
    (buffer-substring-no-properties p1 p2)
))
;; Substrings Delimited by Tokens:5 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:6]]
(cl-defun buffer-substring-delimited-whole-buffer (start end)
  "Return a list of all substrings in the current buffer that
   are delimited by regexp tokens ‘start’ and ‘end’, exclusively.
  "
  (save-excursion
    (let ((l nil) (continue t))
     (beginning-of-buffer)

     (while continue
       (condition-case nil
	 ;; attemptClause
	 (setq l (cons (buffer-substring-delimited start end) l))
	 ;; recoveryBody
	 (error (setq continue nil))))

     ;; We've collected items as we saw them, so ‘l’ is in reverse.
    (reverse l)
    )
  )
)
;; Substrings Delimited by Tokens:6 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:8]]
(cl-defun extract-imports ()
  "Return substring of buffer whose lines mention “import”.
   Throw away any that mention the substring “⟪FileName⟫_Generated”.
  "
  (thread-last (buffer-substring-no-properties (point-min) (point-max))
    (s-split "\n")
    (--filter (s-contains? "import" it))
    (--remove (s-contains?
	       (format  "%s_Generated" (file-name-sans-extension (buffer-name))) it))
    (s-join "\n")
  )
)
;; Substrings Delimited by Tokens:8 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~Itify~:%20A%20macro%20that%20makes%20macros%20%E2%99%A5%E2%80%BF%E2%99%A5][~Itify~: A macro that makes macros ♥‿♥:3]]
(defmacro itify (fname)
  "
   From a function (h f x), obtain a macro (h-it (⋯it⋯) x) that rewrites into
   the orginal such that the first (functional) argument  may now be an expression
   with free variable ‘it’. One declates (itify h) for a named top-level function ‘h’.

   NOTE: Since functions are of the form (cons 'macro-or-fun (function (lambda args body)))
   we can obtain the number of args by getting ‘args’ and taking its length.
   Then we can change any of its indices to take an expression rather than a function.
   Indeed, (macroexpand '(itify ap))
	 ⇒ (defalias (quote ap-it) (cons (quote macro) (function (lambda (itbody more)
	     (list (quote ap) (list (quote lambda) (quote (it)) itbody) more)))))      .
  "

  `(defmacro ,(intern (format "%s-it" (symbol-name fname))) (itbody more)
       (list (quote ,fname) (list 'lambda '(it) itbody) more))
)
;; ~Itify~: A macro that makes macros ♥‿♥:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~Itify~:%20A%20macro%20that%20makes%20macros%20%E2%99%A5%E2%80%BF%E2%99%A5][~Itify~: A macro that makes macros ♥‿♥:5]]
(itify funcall)
;; ~Itify~: A macro that makes macros ♥‿♥:5 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~Itify~:%20A%20macro%20that%20makes%20macros%20%E2%99%A5%E2%80%BF%E2%99%A5][~Itify~: A macro that makes macros ♥‿♥:6]]
(defun rename-mixfix (f op)
  "Given an Agda mixfix operator, apply a function on strings ‘f’ on
   the inner-most delimiting tokens of the operator, in-particular ignoring
   outer argument markers ‘_’.

   For example, if you wish to decorate an operator with a prime or a subscript,
   we cannot simply catenate else we obtain “_⊕_₁” rather than “_⊕₁_”.

   Here are some sample results, assuming “f ≈ (λ (it) (format “₀%s¹” it))”:
   _⊕_     ↦  _₀⊕¹_
   _[_⊗_]  ↦  _₀[_⊗_]¹
   he_lo   ↦  ₀he_lo¹
   he-lo   ↦  ₀he-lo¹
  "

  (let* ((parts (s-split "_" op)) (front (s-blank? (first parts))) (rear (s-blank? (car (last parts)))))

  (--> (concat (when front "_") "$here" (when rear "_"))
       (substring-delimited-$ it op :longest-substring t)
       (funcall f it)
       (concat (when front "_") it (when rear "_"))
   )))

;; Need this for ‘reify-instances’.
(itify rename-mixfix)
;; ~Itify~: A macro that makes macros ♥‿♥:6 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~Itify~:%20A%20macro%20that%20makes%20macros%20%E2%99%A5%E2%80%BF%E2%99%A5][~Itify~: A macro that makes macros ♥‿♥:7]]
(ert-deftest rename-mixfix ()

  (should (equal (rename-mixfix #'identity "_⊕_") "_⊕_"))

  (should (equal "_⊕′_" (rename-mixfix-it (eval (car (read-from-string "(concat it \"′\")"))) "_⊕_")))

  (should  (equal (--map (rename-mixfix-it (format "₀%s¹" it) it) '("_⊕_" "_[_⊗_]" "he_lo" "he-lo"))
       ;; Outermost ‘it’ belongs to --map; inner-most ‘it’ belongs to rename-mixfix-it.
  '("_₀⊕¹_" "_₀[_⊗_]¹" "₀he_lo¹" "₀he-lo¹"))))
;; ~Itify~: A macro that makes macros ♥‿♥:7 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*The%20~package-former~%20Datatype][The ~package-former~ Datatype:2]]
(defstruct package-former
  "Record of components that form a PackageFormer.

   - ‘docstring’: Relevant documentation about this structure; e.g.,
      what is the instance declaration that generated this type, if any.

   - ‘type’: PackageFormer, record, data, module, function, etc.

   - ‘name’: The name of the grouping mechanism schema.

   - ‘level’: The universe level that the instantiations will inhabit.
	      The universe level of the PackageFormer.

   - Finally, the children fields are the typed-names that constitute the body of the
     grouping mechanism. As long as consistent indentation is selected, it does not matter how much.
     As such, we keep track of these indentation numerics ourselves in case we need to tweak them.

   - Internally, the zeroth element always refers to the variation symbol whereas the first element
     refers to the ‘universe of discourse 𝒰’, if any is explicitly provided, and the next ‘waist’-many
     elements are considered parameters. Note that for an ADT, 𝒰 is the ADT name, the 𝒰 of a record
     is the record name, but for a typeclass 𝒰 is generally specfiied as a set, say “Carrier : Set ℓ”.
     TODO: MA: Outdated; eventually need to support variations?
  "
  docstring
  type
  name
  level

  waist ;; Delimits elements into parameters and fields.
  waist-strings

  ;; children
  indentation ;; useful for when new elements are added.
  elements
)
;; The ~package-former~ Datatype:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*The%20~package-former~%20Datatype][The ~package-former~ Datatype:3]]
;; An anaphoric macro ^_^
(defmacro open-pf (p &rest body)
  `(let*
    ((docstring             (package-former-docstring ,p))
     (type                  (package-former-type ,p))
     (name                  (package-former-name ,p))
     (level                 (package-former-level ,p))
     (waist                 (package-former-waist ,p))
     (waist-strings         (package-former-waist-strings ,p))
     (indentation           (package-former-indentation ,p))
     (elements              (package-former-elements ,p))

    ;; It is the user's repsonsibility to pop-off the variation,
    ;; if it is undesirable.
    ;; TODO: MA: Outdated; eventually need to support variations?

    ; (carrier               (nth 1 elements))
    (parameters            (-take waist elements))
    (fields                (-drop waist elements)))
    ,@body
  )
)
;; The ~package-former~ Datatype:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*The%20~package-former~%20Datatype][The ~package-former~ Datatype:4]]
(defun make-tn (name type)
  "Produce a typed-name pair."
  (concat (s-trim name) " : " (s-trim type)))

(defun get-name (tn)
  "Given a string “name : type”, return the ‘name’;
   which will not have any colons in it.
   Whitespace at the edges is trimmed away.
  "
  (s-trim (car (s-split " : " tn))))

(defun get-type (tn)
  "Given a string “name : type”, return the longest possible ‘type’ substring.
  Whitespace at the edges is trimmed away."
  (s-trim (s-join " : " (cdr (s-split " : " tn)))))

;;

(defmacro map-name (fbody tn)
  "Apply string expression ‘fbody’ to the ‘name’ position of a typed-named structure.
   ‘fbody’ may mention ‘name’.
  "
  `(make-tn (rename-mixfix (lambda (name) ,fbody) (get-name ,tn)) (get-type ,tn))
)

(defmacro map-type (fbody tn)
  "Apply string expression ‘fbody’ to the ‘type’ position of a typed-named structure.
   ‘fbody’ may mention ‘type’.
  "
  `(let ((type (get-type ,tn)))
       (make-tn (get-name ,tn) ,fbody))
)

(ert-deftest tn ()
  ;; Superflous space
  (should (equal "name" (get-name "name   : type")))
  ;; Multiple “:”.
  (should (equal "∀ {X : Obj 𝒞} → (X ⟶ X)"
		 (get-type"Id : ∀ {X : Obj 𝒞} → (X ⟶ X)") ))
  )
;; The ~package-former~ Datatype:4 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*The%20~package-former~%20Datatype][The ~package-former~ Datatype:5]]
(defvar package-formers nil
  "The list of PackageFormer schema declarations in the current Agda buffer.")
;; The ~package-former~ Datatype:5 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:1]]
(defun load-package-former (lines)
  "The input ‘lines’ must be a list of lines forming a full PackageFormer declaration;
   e.g., obtained by calling ‘get-children’.

   It is parsed and a ‘package-former’ value is returned.

   - Whitespace is stripped off of items.
   - Docstrings are ignored.
  "

  (if (not lines)
      (error "load-package-former: Error: Input must be non-empty list.")

(catch 'exit
  (let* (pf
	 (header (or (car lines) (throw 'exit nil)))
	 (name (substring-delimited-$ "PackageFormer $here :" header))
	 (level (substring-delimited-$ "Set $here where" header)))

    ;; MA: Replace with a hook.
    ;; (--map (highlight-phrase (s-trim it) 'hi-yellow) (cdr lines))

    (setq pf
       (make-package-former
	:type                     "PackageFormer"
	:name                     name
	;; ‘level’ may be “”, that's okay. It may be a subscript or implicitly zero & so no space after ‘Set’.
	:level                    level
	:waist                    0 ;; TODO: Currently no parameter support for arbitrary PackageFormers.
	:indentation              (get-indentation (cadr lines))
	:elements                 (--map (s-trim it) (cdr lines))
     ))

    (push (cons name pf) package-formers)

    ;; return value
    pf

))))

(ert-deftest pf-parse ()

  ;; Error on empty list of lines.
   (should-error (load-package-former nil))

   ;; No crash on empty line.
   ;; (should (load-package-former (list "")))

   ;; No crash on PackageFormer with no elements.
   (should (load-package-former (list "PackageFormer PF : Set ℓ where")))

   ;; Levels
   (should (equal "ℓ" (package-former-level (load-package-former (list "PackageFormer PF : Set ℓ where")))))
   (should (equal "" (package-former-level (load-package-former (list "PackageFormer PF : Set  where")))))
   (should (equal "₃" (package-former-level (load-package-former (list "PackageFormer PF : Set₃ where")))))
   (should (equal "(Level.suc ℓ)" (package-former-level (load-package-former (list "PackageFormer PF : Set (Level.suc ℓ) where")))))

   ;; Full parsing.
   (-let [pf (load-package-former (cadr (get-children "PackageFormer" test)))]
     (should (equal (format "%s" pf)
		    "#s(package-former nil PackageFormer M-Set ₁ 0 3 (Scalar  : Set Vector  : Set _·_     : Scalar → Vector → Vector 𝟙       : Scalar _×_     : Scalar → Scalar → Scalar leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋 assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)))")))
   )
;; Package Former Parsing and Pretty Printing:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:3]]
(defun special (f)
  "Special elements, for whatever reason are exceptional, and so
   are maked as singleton lists and their indentation is lessened.
   That is, these denote sibling fields rather than more children.

   Special elements include: field, private.

   See ‘show-package-former’ for their use and how their printed.
  "
  (--any? (s-contains? it f) '("field" "private")))
;; Package Former Parsing and Pretty Printing:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:4]]
(cl-defun show-package-former (p &key extra-waist-strings
				 (omit-level nil) omit-docstring omit-car-element)
  "Pretty print a package-former record value.

   -‘waist-strings’: Arbitrary new elements that are input at the location of the
     PackageFormer's waist. E.g., the following results in a new local alias ‘n’
     before the remaining constitutents are printed under a “field” clause.

	 :waist-strings (list “private” “n : ℕ” “n = 3” “field”)
  "

  (open-pf p (s-join "\n" (-cons*

     ;; 0. The documentation string
     (and (not omit-docstring) docstring (format "{- %s -}" docstring))

     ;; 1. The schema declaration
      (s-collapse-whitespace (s-join " " (list type name (s-join " " (--map (concat "(" it ")") parameters)) (unless omit-level (concat ": Set" level))
				    "where")))


     ;; The elements of a PackageFormer
       (thread-last fields

	(-concat waist-strings)
	(-concat extra-waist-strings)

	;; Indent all elements, less indentation for the specials.
	(--map (concat (s-repeat (- indentation (if (special it) 2 0)) " ") it))
	(funcall (if omit-car-element #'cdr #'identity))
	)
    ))))
;; Package Former Parsing and Pretty Printing:4 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Parsing%20an%20Agda%20Buffer][Parsing an Agda Buffer:1]]
(defvar instantiations-remaining nil
  "The PackageFormer instantiations that need to be performed.")
;; Parsing an Agda Buffer:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*List%20of%20~instantiations-remaining~][List of  ~instantiations-remaining~:2]]
(defstruct instance-declaration
  "Record of components for an PackageFormer instance declaration:
   ⟪name⟫ = ⟪package-former⟫ (⟪variation⟫ [⟪args⟫])*
  "

  docstring      ;; What the declaration looks like, useful for reference.
  name           ;; Left-hand side
  package-former ;; Parent grouping mechanism
  alterations    ;; List of variationals along with their arguments.
)
;; List of  ~instantiations-remaining~:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*List%20of%20~instantiations-remaining~][List of  ~instantiations-remaining~:3]]
(cl-defun parse-labelled-to-list (label the-list &key (no-to nil))

     "Given a “to-list” of the form “label (x₀ to y₀; …; xₙ to yₙ; λ x → Bx)”
      yield the Lisp list of dotted pairs “( ((x₀ . y₀) ⋯ (xₙ . yₙ)) “(lambda (x) Bx)”)”
      where the *optional* final clause of the to-list is considered a default or ‘otherwise’
      case and is converted into a legitimate Lisp function.

      No label results in to-list becoming a dotted list.
      When the otherwise clause is absent, it defaults to the identity function.

      If “no-to” is true, then we do not parse the to-clauses, yielding
      a list of strings.

      Errors on an empty list. Yields nil if the label is not found.
      Note that n = 0 is fine, provided the otherwise clause
      is present.
     "

     (when (or (equal (car (s-split " " (s-trim the-list))) label) (s-blank? (s-trim label)))

     (-let* ( ;; (label "var") (the-list "var ()") no-to
	     (result (thread-last the-list

		      ;; Discard identifying label
		      (substring-delimited-$ (format "%s ($here)" label))

		      ;; Split along semicolons.
		      (s-split ";")

		      ;; Removed superflous whitespace
		      (--map (s-trim it))))

	     otherwise var)

       ;; If there is a “otherwise” function to apply,
       ;; then turn it into a Lisp function and drop it
       ;; from the prefix of the to-list. Else, set otherwise to identity.
       (if (not (s-contains? "λ" (car (-take-last 1 result))))

	   (setq otherwise #'identity)

	 ;; Drop the Agda's λ→ in-favour of Lisp's (lambda ⋯).
	 ;; Replace Agda catenation's with Lisp concat.
	 (setq otherwise (thread-last (car (-take-last 1 result))
	       (s-replace "++" " ")
	       (substring-delimited-$ "λ $here")
	       (s-split " → ")
	       (funcall-it (format "(lambda (%s) (concat %s))" (car it) (cadr it)))
	       read-from-string
	       car
	       ))

	 (setq result (-drop-last 1 result)))

       ;; Turn into dotted pairs, unless suggested otherwise.
       ;; Need to ensure ‘result’ is non-empty; since it may
       ;; be a singleton that was dropped into the ‘otherwise’.
       (when (and result (not no-to))
	 (setq result (thread-last result
	     (--map (s-split " to " it))
	     ;; Need to ensure it's a list of pairs; otherwise something went wrong.
	     ;; Suffices to ensure the head element has a second component.
	     (funcall-it (if (cadar it)
		 (--map (cons (s-trim (first it)) (s-trim (second it))) it)
		 (message "parse-labelled-to-list: Is this “to-list” well-formed: %s ⁇" (pp it)) it))))) ;; No desire to error since we may parse non 700-syntax.
       (list result otherwise)
)))
;; List of  ~instantiations-remaining~:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*List%20of%20~instantiations-remaining~][List of  ~instantiations-remaining~:4]]
(ert-deftest parse-tos ()

  ;; Expected use
  (should (equal '(("a" . "b") ("c" . "d")) (car(parse-labelled-to-list "map"  "map (a to b; c to d)"))))
  (should (equal '(("a" . "b")) (car(parse-labelled-to-list "map"  "map (a to b)"))))
  (should (equal '(("a" . "b")) (car(parse-labelled-to-list "map"  "map (a to b; λ x → x)"))))
  (should (equal (lambda (x) (concat x)) (cadr(parse-labelled-to-list "map"  "map (a to b; λ x → x)"))))
  (should (equal (lambda (x) (concat x "′")) (cadr(parse-labelled-to-list "map"  "map (a to b; λ x → x ++ \"′\")"))))
  (should (equal (lambda (x) (concat x "′")) (cadr(parse-labelled-to-list "map" "map (λ x → x ++ \"′\")"))))

  ;; Empty list is fine.
  (should (equal '((("")) identity)  (parse-labelled-to-list "map" "map ()")))

  ;; Singleton list
  (should (equal '(("a" . "b")) (car (parse-labelled-to-list "map"  "map (a to b)"))))
    (should (equal '(("one-arg")) (car (parse-labelled-to-list "map" "map (one-arg)"))))

  ;; No label results in to-list becoming a dotted list.
  (should (equal '(("a" . "b") ("c" . "d")) (car(parse-labelled-to-list ""  "(a to b; c to d)"))))

  ;; Unmatched label.
  (should (equal nil (car(parse-labelled-to-list "mapp"  "map (a to b)"))))

  ;; Not ill-formed list ---one arg list!
  (should (parse-labelled-to-list "map"  "map (a what b)"))
)
;; List of  ~instantiations-remaining~:4 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*List%20of%20~instantiations-remaining~][List of  ~instantiations-remaining~:5]]
(defun load-instance-declaration (line)
  "If the current ‘line’ string is an instance declaration,
   then parse and add it to the list of ‘instantiations-remaining’;
   else do nothing.

   Returns the instance-declaration that was loaded, otherwise nil.

   Whitespace is automatically collopased from ‘line’.
  "

  ;; Example instance declaration:
  ;; “MagmaR = Magma record renaming (Carrier to C; _⨾_ to _∘_)”
  ;; ⇒ ≥4 pieces, separated by spaces, where second item must be an equality.
  ;; Note: (cddddr nil) ≈ nil

  (let* (inst
	 (pieces (s-split " " (s-collapse-whitespace line)))
	 (new-name   (nth 0 pieces))
	 (eqSymb     (nth 1 pieces))
	 (parent     (nth 2 pieces))
	 (variations (nthcdr 3 pieces))
	 alterations
	 label
	 )

    ;; Minimal check that the the declaration is well-formed.
   ;; if nil ;; (not (and (== 4 (length pieces)) (equal (nth 1 pieces) "=") (not (s-blank? (s-trim (nth 0 pieces))))))
   ;;    (message "load-instance-declaration: Declarations should have at least 4 non-empty pieces; %s ⁇" line)
       ;; We do not crash here since we also arbitrary Agda to flow through the 700-comments as well.

  (when (not (or (s-blank? (s-trim new-name)) (not (equal "=" eqSymb)) (not parent)))

     ;; Stick the rest back together.
     (setq variations (s-join " " variations))

     ;; TODO: HACK: For now, variation MUST be seperated by ⟴.
     (setq variations (s-split "⟴" variations))
     ;; This now is a list of items of the shape “var ⟪left-parens⟫ args”.

     (loop for va in variations
	   do (setq label (car (s-split " " (s-trim va))))
	      ;; (push (cons label (parse-labelled-to-list label va)) alterations)
	     (thread-last (s-split ":" (s-join " " (cdr (s-split " " va :omit-nulls)))) ;; Split along “:key value” pairs.
	       (--map (s-split " " it :omit-nulls))      ;; Split along the space to get key and value.
	       cdr
	       (--map (cons (to-lisp (car it))           ;; Transform it into legitimate Lisp.
			    (to-lisp (s-join " " (cdr it)))))
	       (list label)
	       (add-to-list 'alterations)))

     (setq inst (make-instance-declaration
		 :docstring      line
		 :name           (nth 0 pieces)
		 :package-former (nth 2 pieces)
		 :alterations    alterations))

     (add-to-list 'instantiations-remaining inst)

   ;; Return value.
   inst
  )
))

     ;; PackageFormer names are in yellow; instances are are bolded.
     ;; (highlight-phrase (format "%s " (nth 2 pieces)) 'hi-yellow)
     ;; (highlight-phrase (nth 0 pieces) 'bold) ;; 'warning) ;; i.e., orange
     ;;
     ;; MA: Replace with a hook.
;; List of  ~instantiations-remaining~:5 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*List%20of%20~instantiations-remaining~][List of  ~instantiations-remaining~:6]]
(ert-deftest lid ()

  (let (id)

  ;; Basic invocation shape
  ;; “to”! (setq id (load-instance-declaration "NewName = PF var₁ :arg (λ x₁ → B₁) ⟴ var₂ :arg (a to b; λ x₂ → B₂)"))
  (setq id (load-instance-declaration "NewName = PF var₁ :arg₀ (λ x₁ → B₁) :val₀ nice ⟴ var₂ :arg (λ x₂ → B₂)"))
  (cdr (instance-declaration-alterations id))
  (should (equal "NewName" (instance-declaration-name id)))
  (should (equal "PF" (instance-declaration-package-former id)))
  (should (equal "((var₂ ((a . b)) (lambda (x₂) (concat B₂))) (var₁ nil (lambda (x₁) (concat B₁))))"
		 (format "%s" (instance-declaration-alterations id))))

  ;; Ill-formed: LHS name is empty string.
  (should (not (load-instance-declaration " = PF var")))

  ;; Ill-formed: Not even a declaration.
  (should (not (load-instance-declaration "private n : ℕ")))

  ;; Variation has no args.
  (should (load-instance-declaration "LHS = PF var ()"))

  ;; Arbitrary variational
  ;; There are parens around each arg since each should be a pair.
  (should (equal "((some-variational ((arg₀) (…) (argₙ)) identity))" (format "%s" (instance-declaration-alterations (load-instance-declaration
   "LHS = Magma some-variational (arg₀; …; argₙ)")))))
  (should (equal "((some-variational nil (lambda (x) (concat x ′))))" (format "%s" (instance-declaration-alterations (load-instance-declaration
  "LHS = Magma some-variational (λ x → x ++ \"′\")")))))
))
;; List of  ~instantiations-remaining~:6 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~load-700-comments~][~load-700-comments~:1]]
(defvar 700-comments nil
  "The contents of the 700-comments.

   If this variable does not change, we short-circut all processing.
   See step ‘½’ below.
  ")

(defvar porting-list nil
  "List of items in 700-comments that are neither PackageFormer declarations
   nor instantations, and so are ported to the generated file.")
;; ~load-700-comments~:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~load-700-comments~][~load-700-comments~:2]]
(cl-defun load-700-comments ()
  "Parse comments of the form “{-700 ⋯ -}” and add all PackageFormer declarations
   to the ‘package-formers’ list and all instantations to the
   ‘instantiations-remaining’ list.
  "
  (interactive)

  ;; For now, ‘item’ is a PackageFormer, instantiation declaration, or other Agda code.
  (let (item lines 700-cmnts)

  ;; 0. Catenate all 700-comments into a single string.
  (setq 700-cmnts (s-join "\n" (buffer-substring-delimited-whole-buffer "^\{-700" "^-\}")))

  (if (equal 700-comments 700-cmnts) (message "700-comments Unchanged.")

    ;; ½. Update global.
    (setq 700-comments 700-cmnts)

    ;; 1. View comments as a sequence of lines, ignore empty lines ---which are not in our grammar.
    (setq lines (--remove (s-blank? (s-collapse-whitespace it)) (s-lines 700-comments)))

    ;; 2. Traverse the 700-comments:
    ;; If we view a “lhs = rhs” equation, add to global ‘instantiations-remaining’ list.
    ;; If we view a PackageFormer declaration, add to global ‘package-formers’ list.
    (while lines
     (setq item (car lines))

     (if (load-instance-declaration item) (setq lines (cdr lines))

       ;; Else we have a PackageFormer declaration and other possiblly-non-700 items.
       (setq item (get-children "PackageFormer" lines))
       ;; port non-700 items to generated file
       (push (s-join "\n" (car item)) porting-list)
       ;; acknowledge PackageFormer declaration, if any
       (when (cadr item) (load-package-former (cadr item)))
       ;; Update lines to be the unconsidered porition of the wild comments.
       (setq lines (caddr item))))

  (message "Finished parsing 700-comments.")
  )
))
;; ~load-700-comments~:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Variationals][Variationals:1]]
(defvar variationals nil
  "Association list of Agda-user defined variational operators.")

(cl-defun to-lisp (string)
  "Parse Agda ‘string’ to obtain a Lisp expression.

   + (λ x → B)   ↦  (lambda (x) B′)
   + B may contain ++, in which case the result is a ‘concat’.
   - B may not contain ‘→’.

  If B is a parens-enclosed expression, then we expect it to
  already be a legitimate Lisp form and so leave it alone.
  "

  (assert (stringp string))

  (let* ((expr (s-collapse-whitespace string))
	 args
	 (body expr)
	 (isλ (equal "(λ" (s-shared-start "(λ" expr))))

    (when isλ
      (thread-last string
	(s-chop-prefix "(λ")
	(s-chop-suffix ")")
	(s-split "→")
	(setq expr))

      (setq args (car expr))
      (setq body (cadr expr))
    )

    ;; (error "%s" body)

    ;; Ensure ‘body’ is a lisp expression.
    (when  (and (s-blank? (s-shared-start "(" body))
		(s-blank? (s-shared-end ")" body)))

	 (when (and isλ (s-contains? " ++ " body))
	   (thread-last body
	     (s-replace "++" " ")
	     (format "(concat %s)")
	     (setq body)))

	 )

    ;; Realise it as Lisp
    (setq expr (if isλ (format "(lambda (%s) %s)" args body)
		   body))
    (car (read-from-string expr))
))

(ert-deftest to-lisp ()
  (should (equal 'data (to-lisp "data")))
  (should (equal '(list 'a 'b 'c) (to-lisp "(list 'a 'b 'c)")))
  (should (equal '('a 'b 'c) (to-lisp "('a 'b 'c)")))
  (should (equal '("a" "b") (to-lisp "(\"a\" \"b\")")))
  (should (equal '(lambda (x) Bx) (to-lisp "(λ x → Bx)")))
  (should (equal '(lambda (x) (when t x)) (to-lisp "(λ x → (when t x))")))
  (should (equal '(lambda (x) just this) (to-lisp "(λ x → just this")))
  (should (equal '(lambda (x) (concat x "′")) (to-lisp "(λ x → x ++ \"′\")")))
)

(cl-defun load-variationals (&optional string-list)
  "Obtain lines of the buffer that start with “𝒱-”.
   Realise them as Lisp functions.

   If the optional ‘string-list’ is provided, then use
   that instead of searching the buffer. This feature
   has been added on to make the presentation of tests
   and examples easier to digest ---without the mockup
   of fletting ‘buffer-substring-no-properties’ to return
   what could instead be ‘string-list’. It was the addition
   of a simple ‘or’ ---far less than this string explaning it.

   For now, the RHS must be an expression of the form “:key₀ value₀ ⋯ :keyₙ valueₙ”
   - where the valueᵢ are legitmate Lisp expressions
   - and the LHS is an atomic name.

   Note: The space around the “:” is irrelevant; no valueᵢ may contain a colon or an equals sign.

  "
  (let (variations name args)

    (thread-last (or string-list (buffer-substring-no-properties (point-min) (point-max)))
      (s-split "\n")
      (--map (s-collapse-whitespace it))
      (--filter (not (s-blank? (s-shared-start "𝒱-" it))))
      (--map (s-chop-prefix "𝒱-" it))
      (setq variations)

      (--map (s-split "=" it))
      (setq variations)
    )

    (loop for (name-args body) in variations
	  do (setq name-args (s-split " " name-args :omit-nulls))
	     (setq name (car name-args))
	     (setq args (cdr name-args))

	     (thread-last (s-split ":" body :omit-nulls)
	       (--map (s-split " " it :omit-nulls))
	       cdr
	       (--map (cons (to-lisp (car it))
			    (to-lisp (s-join " " (cdr it)))))
	       (list name args)
	       (add-to-list 'variationals)
	  ))

    variationals
))
;; Variationals:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Variationals][Variationals:9]]
(defun target (field)
  "Given a declaration “name : type0 → ⋯ → typeN”, yield “typeN”. "
  (ignore-errors (car (-take-last 1 (s-split "→" field))))
  ;; Ignore errors since field may be nil.
)
;; Variationals:9 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~instantiate~][~instantiate~:1]]
(cl-defun instantiate (id)

  "Given an instance-declaration ‘id’, produce a new PackageFormer.
  "

  (should (instance-declaration-p id))
  (let ((self (copy-package-former (cdr (assoc (instance-declaration-package-former id) package-formers)))) variation op $𝑛𝑎𝑚𝑒)

    ;; “(⁉ 'c)” ≈ Get component c, if present, from op.
    ;;              Moreover, if its result references one of op's arguments
    ;;              then evaluate it (as a Lisp expression)
    ;;              otherwise return it as is.
    (flet ((⁉ (c) (-as-> (cdr (assoc c (cadr op))) 𝓇
		     (if (--any (s-contains? (format "%s" it) (format "%s" 𝓇)) (car op))
			 (eval 𝓇)  𝓇)))
	   ;; Don’t bother generating non-working Agda code: Better see the error now rather than at Agda typechecking.
	   (700-wf (c m) (unless c (error (format "700: %s\n\n\t⇨\t%s\n\t⇨\t%s ≈ %s" m (instance-declaration-docstring id) variation op)))))

      (700-wf self (format "Parent “%s” not defined." (instance-declaration-package-former id)))

      (setf (package-former-docstring self) (instance-declaration-docstring id))
      (setq $𝑛𝑎𝑚𝑒 (instance-declaration-name id))
      (setf (package-former-name self) $𝑛𝑎𝑚𝑒)

	    (loop ;; for (variation args *otherwise*) in (instance-declaration-alterations id)
		  for (variation args) in (instance-declaration-alterations id)
		  do
		  (setq op (cdr (assoc variation variationals)))
		  (700-wf op (format "Variational “%s” not defined." variation))

		  ;; Ensure op is well-formed: It's a list of length two: Arguments and body.
		  (should (= 2 (length op)))

		  ;; Substitute all formal variables for ‘op’ with their values.
		  (loop for arg in (cadr (assoc variation variationals))
			do
			;(setq args (--map (mapcar (lambda (x) (quote x)) it) args))
					; (message-box "%s ; %s; %s" args arg (assoc (intern arg) args))
			(--> (cdr (assoc (intern arg) args)) (700-wf (consp it) (format "Arguments for “%s” must be provided as nonempty ()-enclosed lists." arg)))
			(set (intern arg) (car (cdr (assoc (intern arg) args)))))
			 ;; TODO: MA: Only considering the first argument of a list; for now.

		  ;; :kind ≈ The vocabulary that replaces “PackageFormer”.
		  (when-let ((kind (⁉ 'kind)))
		      (should (symbolp kind))
		      (700-wf (-contains? '(record data module PackageFormer) kind)
			      (format "This kind “%s” is not supported by Agda!\n     Valid kinds: record, data, module, PackageFormer." kind))
		      (setf (package-former-type self) (format "%s" kind)))

		  ;; :waist ≈ The division between parameters and remaining elements.
		  (when-let ((waist (⁉ 'waist)))
		    (700-wf (numberp waist) (format "The “waist” should be a number; which “%s” is not." waist))
		    (setf (package-former-waist self) waist))

		  ;; :waist-strings ≈ Extra strings to insert at the waist position.
		  (when-let ((strings (⁉ 'waist-strings)))
		    (assert (listp strings))
		    (setf (package-former-waist-strings self) strings))

		  ;; :level ≈ Either 'inc or 'dec, for increment or decrementing the level.
		  (when-let ((key (⁉ 'level)) (lvl (package-former-level self))
			     (toLevel (lambda (n) (s-join "" (-concat
					    (-repeat n "Level.suc (") (list "Level.zero") (-repeat n ")")))))
			     (subs `("" "₁" "₂" "₃" "₄" "₅" "₆" "₇" "₈" "₉" ,(funcall toLevel 10))))

		    (700-wf (-contains? '(inc dec) key) "The “level” must be “inc” or “dec”.")

		    (if-let ((here (-elem-index (s-trim lvl) subs)))

		      (setq lvl (pcase key
			('inc (nth (1+ here) subs))
			('dec (nth (1- here) subs))))

		      (setq lvl (pcase key
			('inc (format "Level.suc (%s)" lvl))
			('dec (s-join "suc" (cdr (s-split "suc" lvl :omit-nulls)))))))

		    (setf (package-former-level self) lvl))

		  ;; :alter-elements ≈ Map over the typed name constituents.
		  (when-let ((ae (⁉ 'alter-elements)))
		    (setf (package-former-elements self)
			  (-map ae (package-former-elements self))))
			  ;; (setq fsnew (funcall op otherwise fs)) ;; MA: TODO: Incorporate ‘args’!
		  )
)
      ;; We've just formed a new PackageFormer, which can be modified, specialised, later on.
      (add-to-list 'package-formers (cons (instance-declaration-name id) self))

      (show-package-former self)
  )
)
;; ~instantiate~:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*~instantiate~][~instantiate~:7]]
(defun target (field)
  "Given a declaration “name : type0 → ⋯ → typeN”, yield “typeN”. "
  (ignore-errors (car (-take-last 1 (s-split "→" field))))
  ;; Ignore errors since field may be nil.
)
;; ~instantiate~:7 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Instantiate%20all%20items%20in%20~instantiations-remaining~][Instantiate all items in ~instantiations-remaining~:1]]
;; Function combinators; e.g., -partial/-cut, -const, -compose, -orfn & -andfn for generalised ∃/∀.
(use-package dash-functional) ;; https://github.com/magnars/dash.el
;; Instantiate all items in ~instantiations-remaining~:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Instantiate%20all%20items%20in%20~instantiations-remaining~][Instantiate all items in ~instantiations-remaining~:2]]
(cl-defun reify-instances ()
 "Instantiate all items in ‘instantiations-remaining’."

 (interactive)

 (let* (result)

   ;; We parsed them top-down, so they're in the wrong order.
   ;; Order matters since declarations yield new PackageFormers
   ;; which may be used in subsequent declarations.
   (dolist (inst (reverse instantiations-remaining))

     ;; Add to list of results. The empty string yields a new line between each generated instantiation.
      (setq result (-cons* (instantiate inst) "" result))
     )

   ;; Output results as a string.
     (s-join "\n" (reverse result))
))
;; Instantiate all items in ~instantiations-remaining~:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Advising%20our%20Beloved%20~C-c%20C-l~][Advising our Beloved ~C-c C-l~:1]]
(defun insert-generated-import (name-of-generated-file)
  "In the current file, find the top-most module declaration
   then insert an import of the generated file.
  "
  (interactive)

  (save-excursion
    (beginning-of-buffer)
    (condition-case the-err
      ;; attemptClause:
      (re-search-forward (concat "open import " name-of-generated-file))
       ;; recoveryBody:
      (error ;; (message-box (format "%s" the-err))
	 (re-search-forward "\\(module.*\\)")
	 (replace-match (concat "\\1\nopen import " name-of-generated-file))
	)
    )
  )
)
;; Advising our Beloved ~C-c C-l~:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Advising%20our%20Beloved%20~C-c%20C-l~][Advising our Beloved ~C-c C-l~:2]]
(defun reify-package-formers (orig-fun &rest args)
  (interactive)

  (let (generated-file-name
	(parent-imports (extract-imports))
       )

  ;; Sometimes we may want the full name due to files being in a nested
  ;; directory hierarchy: (file-name-sans-extension buffer-file-name)
  (setq generated-file-name (concat(file-name-sans-extension (buffer-name))
		  "_Generated"))

  ;; Load variationals, PackageFormers, instantiations, and porting list.
  ;; Setting the following to nil each time is not ideal.
  (setq	variationals              nil
	package-formers           nil
	instantiations-remaining  nil
	700-comments              nil
	porting-list              nil)

  (load-variationals)
  (load-700-comments)

  (with-temp-buffer
    (beginning-of-buffer)

    ;; Copy/paste imports from parent file.
    (insert (s-join "\n" `(
	     "{- This file is generated ;; do not alter. -}\n"
	     ,parent-imports
	     "open import Level as Level"
	     ,(format "module %s where " generated-file-name)
	     , (s-join "\n" porting-list)
	     ,(reify-instances))))

    (write-region (beginning-of-buffer) (end-of-buffer)
		  (concat generated-file-name ".agda"))
    )

  (insert-generated-import generated-file-name)
  )

  ;; Need to revert buffer to discard old colours.
  ;; (save-buffer) (revert-buffer t t t)

  ;; call agda2-load
  (apply orig-fun args)

   ;; Colour 700 keywords
  ;; (loop for kw in '("PackageFormer" "Variation" "hiding" "renaming" "unbundling" "exposing" "renaming" "with")
  ;;  do (highlight-phrase kw 'hi-green))
  ;; Replace with a hook.

  (highlight-phrase "700" 'error)

  (message "700 ∷ All the best coding! (•̀ᴗ•́)و")
)

(advice-add 'agda2-load :around #'reify-package-formers)
;; Advising our Beloved ~C-c C-l~:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Menu%20matter][Menu matter:1]]
(defvar 700-menu-bar (make-sparse-keymap "700 PackageFormers"))

(define-key global-map [menu-bar 700menu] (cons "700PackageFormers" 700-menu-bar))
;; Menu matter:1 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Menu%20matter][Menu matter:2]]
(define-key 700-menu-bar [enable-package-formers]
  '(menu-item "Enable PackageFormer Generation" enable-package-formers))

(defun enable-package-formers ()
 (interactive)
 (advice-add 'agda2-load :around #'reify-package-formers)
 (message-box "C-c C-l now reifies “700-comments” into legitimate Agda.")
)
;; Menu matter:2 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Menu%20matter][Menu matter:3]]
(define-key 700-menu-bar [disable-package-formers]
  '(menu-item "Disable PackageFormer Generation" disable-package-formers))

(defun disable-package-formers ()
 (interactive)
 (advice-remove 'agda2-load #'reify-package-formers)
 (setq global-mode-string (remove "700 (•̀ᴗ•́)و " global-mode-string))
  (message-box "C-c C-l now behaves as it always has.")
)
;; Menu matter:3 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Menu%20matter][Menu matter:4]]
(define-key 700-menu-bar [package-formers-about]
  '(menu-item "About PackageFormers" package-formers-about))

(defun package-formers-about ()
 (interactive)
 (switch-to-buffer "*PackageFormer-About*") (insert
  " This is an editor extension prototyping “the next 700 module systems” proposed research.

    An informal documentation, with examples, page can be found at
    https://alhassy.github.io/next-700-module-systems-proposal/PackageFormer.html

    The technical matter can be found at https://alhassy.github.io/next-700-module-systems-proposal/

    If you experience anything “going wrong” or have any ideas for improvement,
    please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥
  "
 )
)
;; Menu matter:4 ends here

;; [[file:~/thesis-proposal/PackageFormer.org::*Menu%20matter][Menu matter:5]]
(define-minor-mode 700-mode
    "This is an editor extension prototyping “the next 700 module systems” proposed research.

    An informal documentation, with examples, page can be found at
    https://alhassy.github.io/next-700-module-systems-proposal/PackageFormer.html

    The technical matter can be found at https://alhassy.github.io/next-700-module-systems-proposal/

    If you experience anything “going wrong” or have any ideas for improvement,
    please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥
  "
  :lighter " 700 (•̀ᴗ•́)و)" ;; Icon to display indicating the mode is enabled.
  :require 'foo

  ;; Toggle the menu bar
  ;; (define-key global-map [menu-bar 700menu] t)(not 700-mode))
  (define-key global-map [menu-bar 700menu] (and 700-mode (cons "700PackageFormers" 700-menu-bar)))

  (letf (( (symbol-function 'message-box) #'message))
  (if 700-mode
      ;; Initilisation
      (enable-package-formers)

      ;; Closing
      (disable-package-formers)
  ))

)
;; Menu matter:5 ends here
