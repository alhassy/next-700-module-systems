;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Forming%20Syntax%20and%20the%20Special%20~$%F0%9D%91%9B%F0%9D%91%8E%F0%9D%91%9A%F0%9D%91%92~%20Variable][Forming Syntax and the Special ~$𝑛𝑎𝑚𝑒~ Variable:1]]
(defun target (thing)
  " Given a declaration “name : type0 → ⋯ → typeN”, yield “typeN”. "
  (car (-take-last 1 (s-split "→" thing)))
)
;; Forming Syntax and the Special ~$𝑛𝑎𝑚𝑒~ Variable:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Finding%20Children%20in%20the%20Wild][Finding Children in the Wild:3]]
(defun get-indentation (string)
  "How many spaces are there at the front of ‘string’?

  Property: The resulting number is ‘≤ length string’.
  "
  (if string (length (s-shared-start string (s-repeat (length string) " "))) 0)
)
;; Finding Children in the Wild:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Finding%20Children%20in%20the%20Wild][Finding Children in the Wild:4]]
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

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Finding%20Children%20in%20the%20Wild][Finding Children in the Wild:13]]
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

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:1]]
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

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:2]]
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

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:3]]
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

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:5]]
(cl-defun buffer-substring-delimited (start end &optional more)
  "
  Get the current buffer's /next/ available substring that is delimited
  between the regexp tokens ‘start’ up to ‘end’, exclusively.

  If no tokens are found, an error is thrown.

  ‘more’ is a function that is called on the found instance:
  It is a function of the start and end positions of the occurance.
  "
  (let (start-pos end-pos sp ep content)
    (re-search-forward start)
    (setq start-pos (point))
    (backward-word)
    (setq sp (point))

    (re-search-forward end)
    (setq ep (point))
    (backward-word)
    (setq end-pos (point))

    (setq content  (buffer-substring-no-properties start-pos end-pos))

    (when more (funcall more sp ep))
    (when 700-folding
      (goto-char start-pos)
      (push-mark end-pos)
      (setq mark-active t)
      (fold-active-region start-pos end-pos))

    content))
;; Substrings Delimited by Tokens:5 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:6]]
; (use-package fold-this :demand t :ensure t)
(defvar 700-folding nil
  "Should 700 and lisp blocks be folded away when C-c C-l.")
;; Substrings Delimited by Tokens:6 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Substrings%20Delimited%20by%20Tokens][Substrings Delimited by Tokens:7]]
(cl-defun buffer-substring-delimited-whole-buffer (start end &optional more)
  "Return a list of all substrings in the current buffer that
   are delimited by regexp tokens ‘start’ and ‘end’, exclusively.

  ‘more’ is a function that is called on the found instance:
  It is a function of the start and end positions of the occurance.
  "
  ;; Colour 700 keyword red “'error”
  (highlight-phrase start 'error)
  (save-excursion
    (let ((l nil) (continue t))
     (beginning-of-buffer)

     (while continue
       (condition-case nil
     ;; attemptClause
     (setq l (cons (buffer-substring-delimited start end more) l))
     ;; recoveryBody
     (error (setq continue nil))))

     ;; We've collected items as we saw them, so ‘l’ is in reverse.
    (reverse l))))
;; Substrings Delimited by Tokens:7 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Agda%20Mixfix%20Renaming%20and%20Imports][Agda Mixfix Renaming and Imports:1]]
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
;; Agda Mixfix Renaming and Imports:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Agda%20Mixfix%20Renaming%20and%20Imports][Agda Mixfix Renaming and Imports:2]]
(cl-defun extract-imports ()
  "Return substring of buffer whose lines mention “import”.
   Throw away any that mention the substring “⟪FileName⟫_Generated”.
  "
  (thread-last (buffer-substring-no-properties (point-min) (point-max))
    (s-split "\n")
    (--filter (s-contains? "import " it))
    (--remove (s-contains?
           (format  "%s_Generated" (file-name-sans-extension (buffer-name))) it))
    (s-join "\n")
  )
)
;; Agda Mixfix Renaming and Imports:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*The%20~package-former~%20Datatype][The ~package-former~ Datatype:2]]
(defstruct package-former
  "Record of components that form a PackageFormer.

   - ‘docstring’: Relevant documentation about this structure; e.g.,
      what is the instance declaration that generated this type, if any.

   - ‘kind’: PackageFormer, record, data, module, function, etc.

   - ‘name’: The name of the grouping mechanism schema.

   - ‘level’: The universe level that the instantiations will inhabit.
          The universe level of the PackageFormer.

   - Finally, the children fields are the typed-names that constitute the body of the
     grouping mechanism. As long as consistent indentation is selected, it does not matter how much.
     As such, we keep track of these indentation numerics ourselves in case we need to tweak them.

   - The first ‘waist’-many elements are considered parameters.

   ‼ TODO: Eventually need to support variations?
  "
  docstring
  kind
  name
  level

  waist ;; Delimits elements into parameters and fields.
  waist-strings

  ;; children
  indentation ;; useful for when new elements are added.
  elements
)
;; The ~package-former~ Datatype:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*The%20~package-former~%20Datatype][The ~package-former~ Datatype:3]]
(defvar package-formers nil
  "The list of PackageFormer schema declarations in the current Agda buffer.")
;; The ~package-former~ Datatype:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Locally%20Opening%20a%20PackageFormer][Locally Opening a PackageFormer:1]]
;; An anaphoric macro ^_^
(defmacro open-pf (p &rest body)
  `(let*
    ((docstring             (package-former-docstring ,p))
     (kind                  (package-former-kind ,p))
     (name                  (package-former-name ,p))
     (level                 (package-former-level ,p))
     (waist                 (package-former-waist ,p))
     (waist-strings         (package-former-waist-strings ,p))
     (indentation           (package-former-indentation ,p))
     (elements              (package-former-elements ,p))

    ;; ‼ TODO: MA: Eventually need to support variations?

    (parameters            (-take waist elements))
    (fields                (-drop waist elements)))
    ,@body
  )
)
;; Locally Opening a PackageFormer:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Typed%20Names][Typed Names:1]]
(defun make-tn (name type)
  "Produce a typed-name pair; discard all surrounding whitespace."
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
;; Typed Names:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:1]]
(defun load-package-former (lines)
  "The input ‘lines’ must be a list of lines forming a full PackageFormer declaration;
   e.g., obtained by calling ‘get-children’.

   It is parsed and a ‘package-former’ value is returned.

   - Whitespace is stripped off of items.
   - Docstrings are ignored.
  "

  (when (not lines)
      (error "load-package-former: Error: Input must be non-empty list."))

  (catch 'exit
    (let* (pf
           (header (or (car lines) (throw 'exit nil)))
           (name (substring-delimited-$ "PackageFormer $here :" header))
           (level (substring-delimited-$ "Set $here where" header)))

      (when 700-highlighting
        (--map (highlight-phrase (s-trim it) 'hi-yellow) (cdr lines)))

      (setq pf
            (make-package-former
             :kind                     "PackageFormer"
             :name                     name
             ;; ‘level’ may be “”, that's okay.
             ;; It may be a subscript or implicitly zero & so no space after ‘Set’.
             :level                    level
             :waist                    0
             ;; ‼ TODO: Currently no parameter support for arbitrary PackageFormers.
             :indentation              (get-indentation (cadr lines))
             :elements  (--remove (s-starts-with? "-- " it) (--map (s-trim it) (cdr lines)))
             ))

      (push (cons name pf) package-formers)

      ;; return value
      pf)))
;; Package Former Parsing and Pretty Printing:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:3]]
(defun special (f)
  "Special elements, for whatever reason are exceptional, and so
   are maked as singleton lists and their indentation is lessened.
   That is, these denote sibling fields rather than more children.

   Special elements include: field, private.

   See ‘show-package-former’ for their use and how their printed.
  "
  (--any? (s-contains? it f) '("field" "private" "open" "top-level" "sibling")))
;; Package Former Parsing and Pretty Printing:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:4]]
(cl-defun show-package-former (p &key extra-waist-strings
                 omit-docstring omit-car-element)
  "Pretty print a package-former record value.

   -‘waist-strings’: Arbitrary new elements that are input at the location of the
     PackageFormer's waist. E.g., the following results in a new local alias ‘n’
     before the remaining constitutents are printed under a “field” clause.

     :waist-strings (list “private” “n : ℕ” “n = 3” “field”)
  "

  (open-pf p
    (s-join "\n"
      (-cons*

       ;; The documentation string
       (and (not omit-docstring) docstring (format "{- %s -}" docstring))

       ;; The schema declaration
       (s-collapse-whitespace
        (s-join " "
                (list kind
                      name
                      (s-join " " (--map (concat "(" it ")") parameters))
                      (unless (equal level 'none) (concat ": Set" level))
                      "where")))

       ;; The elements of a PackageFormer
       (thread-last fields
         (-concat waist-strings)
         (-concat extra-waist-strings)

         ;; Indent all elements, less indentation for the specials.
         ;; Regarding “top-level” see the “recordₑ” variational in Paper0.pdf.
         ;; The extra whitespace is important.
         (--map (concat (s-repeat (- indentation (if (special it) 2 0)) (if (s-starts-with? "sibling" it) "" " "))
                        (if (s-starts-with? "top-level" it) (s-chop-prefix "top-level " it)
                          (if (s-starts-with? "sibling" it) (s-chop-prefix "sibling " it) it))))
         (funcall (if omit-car-element #'cdr #'identity)))))))
;; Package Former Parsing and Pretty Printing:4 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Package%20Former%20Parsing%20and%20Pretty%20Printing][Package Former Parsing and Pretty Printing:8]]
(ert-deftest pf-parse ()

  ;; Error on empty list of lines.
   (should-error (load-package-former nil))

   ;; No crash on empty line.
   (should (load-package-former (list "")))

   ;; No crash on PackageFormer with no elements.
   (should (load-package-former (list "PackageFormer PF : Set ℓ where")))

   ;; Levels
   (should (equal "ℓ" (package-former-level (load-package-former (list "PackageFormer PF : Set ℓ where")))))
   ;;
   (should (equal "" (package-former-level (load-package-former (list "PackageFormer PF : Set  where")))))
   ;;
   (should (equal "₃" (package-former-level (load-package-former (list "PackageFormer PF : Set₃ where")))))
   ;;
   (should (equal "(Level.suc ℓ)" (package-former-level (load-package-former (list "PackageFormer PF : Set (Level.suc ℓ) where")))))

   ;; Full parsing.
   (-let [pf (load-package-former (cadr (get-children "PackageFormer" test)))]
     (equal (format "%s" pf)
            "#s(package-former nil PackageFormer M-Set ₁ 0 nil 3 (Scalar  : Set Vector  : Set _·_     : Scalar → Vector → Vector 𝟙       : Scalar _×_     : Scalar → Scalar → Scalar leftId  : {𝓋 : Vector}  →  𝟙 · 𝓋  ≡  𝓋 assoc   : {a b : Scalar} {𝓋 : Vector} → (a × b) · 𝓋  ≡  a · (b · 𝓋)))"))

  (-let [pf (cadr (get-children "PackageFormer" test))]
    (should (equal (s-concat "\n" (s-join "\n" pf))
                   (show-package-former (load-package-former pf)))))

)
;; Package Former Parsing and Pretty Printing:8 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*%F0%9D%92%B1%F0%9D%92%B8,%20%F0%9D%92%B1-,%20and%20%F0%9D%92%B1][𝒱𝒸,  𝒱-, and 𝒱:1]]
(defvar *parent-context* nil
  "For error report; what is the current parent context of a child item.

   Should be set whenver a parent invokes a child.
   Since we have no grandchildren, we only need one level.
")

(defun 𝒱𝒸 (body-list &optional context args)
  "Parse a single 𝒱ariational 𝒸lause, as a list, of the form “[label] (:key :value)*”.

   If there is a ‘label’, then yield ‘(label :key value ⋯)’
   since ‘label’ is assumed to exist as a variational having the given
   keys as arguments. The result should be a list of pairs.

   If there is no label, the parse the list of pairs.

  For example,
     (cl-defun 𝒱-test (&key height kind) (format \"%s & %s\" height kind))
     (𝒱₁ '(test :height 3 :kind 'data)) ⇒ “3 & data” ≈ (test :height 3 :kind data)
     (𝒱₁ '(     :height 3 :kind data)) ⇒ ((:height . 3) (:kind . data))

   Newer items c₀ ⟴ ⋯ ⟴ cₙ should be at the front of the list;
   access should then be using ‘assoc’.
  "

  (let* (res (*parent-context* context))
    (loop for clause in (-split-on '⟴ body-list)
          do (setq res (-concat
                 ;; Symbols starting with “:” are keywords.
                 (if (not (keywordp (car clause)))
                     ;; Function invocation case
                     ;; We turn everything into a string so that we may
                     ;; prepend the function name with a 𝒱-
                     ;; then turn that into Lisp with the first eval
                     ;; then invoke the resulting function call with the second eval.
                     (eval `( ,(𝒱- (car clause)) ,@(cdr clause)))
                   ;; List of key-value pairs
                   `,(loop for key   in clause by #'cddr
                           for value in (cdr clause) by #'cddr
                           collect (700-wf key value context args)))  ;; “700-wf” is just a fancy “cons”.
                 ;; Newer items c₀ ⟴ ⋯ ⟴ cₙ should be at the front of the list;
                 ;; access should then be using assoc.
                 res)))
    res))
;; 𝒱𝒸,  𝒱-, and 𝒱:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*%F0%9D%92%B1%F0%9D%92%B8,%20%F0%9D%92%B1-,%20and%20%F0%9D%92%B1][𝒱𝒸,  𝒱-, and 𝒱:2]]
(defun 𝒱- (name)
  "Prefix the Lisp data ‘name’ with a “𝒱-”
   then yield that as a Lisp datum.
  "
  (should (symbolp name))
  (thread-last name
    (format "𝒱-%s")
    read-from-string
    car))
;; 𝒱𝒸,  𝒱-, and 𝒱:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*%F0%9D%92%B1%F0%9D%92%B8,%20%F0%9D%92%B1-,%20and%20%F0%9D%92%B1][𝒱𝒸,  𝒱-, and 𝒱:3]]
(defmacro 𝒱 (name &rest body)

  "Reify as Lisp a variational declaration using the following grammar.

        𝓋   ::= [docstring] identifier (identifier)* = 𝓋𝒸
        𝓋𝒸  ::= [identifier] (:key value)* (⟴ 𝓋𝒸)*

    The resulting generated function has its code embeded as a docstring viewable
    with “C-h o” ---catented after any provided user documentation.
  "

  ;; For beauty, let's colour variational names green.
  ;; Only colour occurances that have a space before or after.
  (when 700-highlighting
    (highlight-phrase (format "[- \\| ]%s " `,name) 'hi-green))

  ;; Main code follows.
  (let* ((context (mapconcat (lambda (x) (prin1-to-string x t)) (cons name body) " "))
         (args-body (-split-on '= body)) args docs body res actual-code)
    (pcase (length args-body)
      (2 (setq args (car args-body)
               body (cadr args-body)))
      (t (setq body (car args-body))))

    ;; Set any documentation string and reify the body's variational clauses.
    (when (stringp (car body)) (setq docs (car body) body (cdr body)))
    (setq res (𝒱𝒸 body context args))

    ;; I want to be able to actually, visually, see the resulting
    ;; generated definition of a function.
    ;; Hence, I embed its source code as a string in the code.
    ;;
    ;; I'm using strings so that they appear in the docstring via C-h o.
    ;;
    (setq actual-code
    `(cl-defun ,(𝒱- name) (&key ,@args)

       ;; Stage the formal names *now*, then evaluate their values at run time.
       ;; Traverse the list of pairs and change the nested formal names with the
       ;; given values. Praise the Lord!
      (let* ((give-goal (quote ,res)) (give-goal₀ give-goal))
        (when (quote ,args)

          "Stage the formal names *now*, then evaluate their values at run time."
          (loop for a in (quote ,args)
                do (setq give-goal (subst (eval a) a give-goal)))

          ;; TODO, maybe.
          ;; "Check that substituted values are well-typed"
          ;; (--map (700-wf (car it) (or (cdr it)
          ;;                             ;; Mention which argument is not supplied.
          ;;                             (format "No Value for :%s Provided!"
          ;;                                     (cdr (assoc (car it) (reverse give-goal₀)))))
          ;;                (s-concat (when *parent-context* (s-concat *parent-context* "\n\t➩\t")) ,context)) give-goal)

          )

         give-goal)))

    ;; Now set the code as a documentation string in it, after the fact.
    (setq docs (format "Arguments:\t%s\n%s" args
                       (if (not docs) "Undocumented user-defined variational."
                         ;; Keep paragraph structure, but ignore whitespace otherwise.
                         (thread-last docs
                           (s-split "\n\n")
                           (mapcar #'s-collapse-whitespace)
                           (mapcar #'s-trim)
                           (s-join "\n\n")
                           (s-word-wrap 70)
                           (format "\n%s\n\n\n")))))
                    ;; When the user provides documentation, they may not want to see
                    ;; the raw and expansions, so we pad extra whitespace before them.

    (put (𝒱- name) 'function-documentation
         (format "%s\n⟪User Definition⟫\n\n%s\n\n⟪Lisp Elaboration⟫\n\n%s"
                 docs context (pp-to-string actual-code)))
    ;; Register this new item in our list of variationals.
    (push (cons name docs) variationals)
    ;; Return value:
    actual-code))
;; 𝒱𝒸,  𝒱-, and 𝒱:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Well-formed%20checks%20---Error%20reporting][Well-formed checks ---Error reporting:1]]
(defun 700-error (condition message context)
  "Ensure ‘condition’ is true, otherwise emit ‘message’
   and indicate the offending ‘context’.
  "
  (when condition
    (error (format "700: %s\n\n\t⇨\t%s" message context))))
;; Well-formed checks ---Error reporting:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Well-formed%20checks%20---Error%20reporting][Well-formed checks ---Error reporting:2]]
(cl-defun 700-wf (key value &optional context args)
  "This operation checks that the ‘value’ of ‘key’
   is well-formed according to 700-specifications ---which are stated
   explicitly within this method--- and if it is well-formed we
   return the ‘value’ /interpreted/ along with the ‘key’.

   When the value is not well-formed, we use the provided ‘context’
   in an error message. No error is reported if ‘value’ is an ‘arg’ument
   of a variational begin declared.
  "

  (let ( condition message
         (wf '( (:kind   (-contains? '(record data module PackageFormer) value)
                         (format "This kind “%s” is not supported by Agda!\n     Valid kinds: record, data, module, PackageFormer." value))
                (:waist  (numberp value) (format "The waist should be a number; which “%s” is not." value))
                (:waist-strings (listp value) (format "The waist-strings should be a Lisp list of strings; which “%s” is not." value))
                (:level (-contains? '(inc dec none) value) (format "The “level” must be “inc” or “dec” or “none”; which “%s” is not." value))
                (:alter-elements (functionp value) (format "Componenet alter-elements should be a function; which “%s” is not." value))
                       )))

    (when-let ((here (assoc key wf)))
      (setq condition        (eval (nth 1 here))
            message          (eval (nth 2 here)))
      (700-error (not (or condition (-contains? args value))) message context))

    ;; Return the key-value as a pair for further processing.
    ;; :kind and :level values are symbols and so cannot be evaluated furthur.
    (cons key
          (if
           (or (-contains? args value) (-contains? '(:kind :level :waist-strings) key))
           value
           (eval value)))))
;; Well-formed checks ---Error reporting:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Loading%20Variationals:%20Super%20Simple%20Conversion%20From%20String%20to%20Lisp][Loading Variationals: Super Simple Conversion From String to Lisp:1]]
(cl-defun load-variational (variation-string)
  "Obtain lines of the buffer that start with “𝒱-”.
   Realise them as Lisp association lists.

   A line is something like:

      𝒱-name x₀ … xₙ  =  ([label₀] :key₀ val₁ ⋯ :keyₘ valₘ ⟴)*

   The result is a list of 3-tuples (name (x₀ ⋯ xₙ) ((key₀ val₀) ⋯ (keyₘ valₘ))),
   containing the clause's name, argument list, and key-value pairs.

   If the optional ‘string-list’ is provided, then use
   that instead of searching the buffer. This feature
   has been added on to make the presentation of tests
   and examples easier to digest ---without the mockup
   of fletting ‘buffer-substring-no-properties’ to return
   what could instead be ‘string-list’. It was the addition
   of a simple ‘or’ ---far less than this string explaning it.

   For now, the RHS must be an expression of the form “:key₀ value₀ ⋯ :keyₙ valueₙ”
   - where the valueᵢ are legitmate Lisp expressions
   - and the LHS is an atomic name, possibly with argument names.
  "

  (thread-last variation-string
    (s-replace "𝒱-" "𝒱 ")
    (format "(%s)")
    read-from-string
    car
    eval))
;; Loading Variationals: Super Simple Conversion From String to Lisp:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Loading%20Variationals:%20Super%20Simple%20Conversion%20From%20String%20to%20Lisp][Loading Variationals: Super Simple Conversion From String to Lisp:2]]
(ert-deftest variationals-𝒱𝒸 ()

  (should (equal (𝒱- 'nice)
                 '𝒱-nice))

  (should (equal (𝒱𝒸 '(:height 3 :kind 'data))
                '((:height . 3) (:kind . data))))


  ;; Error along with “noice”.
  (should-error (𝒱𝒸 '(:height 3 :kind datda) 'noice nil))

  ;; nice error.
  (should-error (𝒱𝒸 '(:level 3)))

  ;;
  (cl-defun 𝒱-test (&key height kind) `( (first . ,height) (second . ,kind)))
  ;;
  (should (equal (𝒱𝒸 '(test :height 3 :kind 'three ⟴ :kind 'module))
                 '((:kind . module) (first . 3) (second . three))))
  ;;
  ;; NOTE: 𝒱-tests′ :kind is optional
  (should (equal (𝒱𝒸 '(test :height 3 ⟴ :kind 'module))
                 '((:kind . module) (first . 3) (second))))
  ;;
  (should (equal (𝒱𝒸 '(:height 3 ⟴ :kind 'module))
                 '((:kind . module) (:height . 3))))

  ;; Recursively place 3 (new) wherever 'it (old) occurs.
  ;; This' a standard Lisp utility.
  (should (equal
           (subst 3 'it '(1 2 it 4 (5 it) 7 (+ 8 it)))
           '(1 2 3 4 (5 3) 7 (+ 8 3))))
)
;; Loading Variationals: Super Simple Conversion From String to Lisp:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Loading%20Variationals:%20Super%20Simple%20Conversion%20From%20String%20to%20Lisp][Loading Variationals: Super Simple Conversion From String to Lisp:3]]
(ert-deftest variationals-𝒱 ()

  ;; Nullary
  (should (𝒱 test₀  = :kind 'record :waist 3))
  (should (equal (𝒱-test₀)
               '((:kind . record) (:waist . 3))))

  ;; Unary
  (should (𝒱 test₁ heightish = :kind 'record :waist heightish))
  (should (equal (𝒱-test₁ :heightish 6)
                 '((:kind . record) (:waist . 6))))

  ;; Invoking the previously defined variational
  (should (𝒱 test₂  = :kind 'data ⟴ test₁ :heightish 2))
  (should (equal (𝒱-test₂)
                 '((:kind . record) (:waist . 2) (:kind . data))))

  ;; See a nice error message ^_^
  (should-error (𝒱 test₃ = :kind recordd))
)
;; Loading Variationals: Super Simple Conversion From String to Lisp:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Loading%20Variationals:%20Super%20Simple%20Conversion%20From%20String%20to%20Lisp][Loading Variationals: Super Simple Conversion From String to Lisp:4]]
(ert-deftest variationals-loading ()

  (should (load-variational "𝒱-tc this height = :level this :waist height"))

  ;; NEATO! (Has desired error)
  ;; (-let [*parent-context* "woadh"]
  ;;   (𝒱-tc :height 'no :this 'inc))
  ;;
  ;; Does not pass: I've commented out the type checking in 𝒱 above, for now.

  (should (𝒱-tc :height 9 :this 'inc))

  (should (equal (𝒱𝒸 '(:a 'b ⟴ tc :height 1))
                 '((:level) (:waist . 1) (:a . b))))

;
)
;; Loading Variationals: Super Simple Conversion From String to Lisp:4 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Loading%20an%20Instance%20---The%20Core%20Utility][Loading an Instance ---The Core Utility:2]]
(defstruct instance-declaration
  "Record of components for an PackageFormer instance declaration:
   ⟪name⟫ = ⟪package-former⟫ (⟴ ⟪variation⟫ [⟪args⟫])*
  "

  docstring      ;; What the declaration looks like, useful for reference.
  name           ;; Left-hand side
  package-former ;; Parent grouping mechanism
  alterations    ;; List of variationals along with their arguments.
)
;; Loading an Instance ---The Core Utility:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Loading%20an%20Instance%20---The%20Core%20Utility][Loading an Instance ---The Core Utility:3]]
(defun load-instance-declaration (line &optional show-it)
  "If the current ‘line’ string is an instance declaration,
   then produce a new PackageFormer from it. Else, do nothing.

   ⇒ Whitespace is automatically collopased from ‘line’.
   ⇒ Nil elements are discarded; e.g., due to a filter.
   ⇒ Duplicates are discarded; e.g., due to a rename.

   Variational clauses may mention
   ⇒ $𝑛𝑎𝑚𝑒: The name of the PackageFormer currently being declared; i.e., the LHS name.
   ⇒ $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠: Many variationals will act on individal elements, but may check a
              property relative to all elements and this name allows us to avoid
              having variationals that simply accomodate for binary functions
              that operate on an individual element while also needing to refer to all
              elements. For example, a variational that keeps an element if it's related
              to another element somehow.
  "

  (letf* (
     (pieces (s-split " " (s-collapse-whitespace line)))
     ($𝑛𝑎𝑚𝑒      (nth 0 pieces))
     ($𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠    nil)
     (eqSymb     (nth 1 pieces))
     ($𝑝𝑎𝑟𝑒𝑛𝑡     (nth 2 pieces))
     (variations (nthcdr 3 pieces))
     (alterations nil)
     (self (copy-package-former (cdr (assoc $𝑝𝑎𝑟𝑒𝑛𝑡 package-formers))))
     ((symbol-function '⁉)
      ;; If componenet ‘c’ is in the ‘alterations’ list of the instance declaration,
      ;; then evalaute any given ‘more’ code, get the value for ‘c’ and turn it
      ;; into a string, if ‘str’ is true, then set the new PackageFormer's ‘c’
      ;; componenet to be this value.
      ;; Well-formedness checks happen at the 𝒱 and 𝒱𝒸 stages, see below.
         (lambda (c &optional str more) (when-let ((it (cdr (assoc (intern (format ":%s" c)) alterations))))
                           (eval `(progn ,@more))
                           (when str (setq it (format "%s" it)))
                           (eval `(setf (,(car (read-from-string (format "package-former-%s" c))) self) it))))

        )
     )

   ;; Ensure instance declaration is well-formed.
    (700-error (or (s-blank? (s-trim $𝑛𝑎𝑚𝑒)) (not (equal "=" eqSymb)) (not $𝑝𝑎𝑟𝑒𝑛𝑡))
               (concat "An instance declaration is of the form "
                       "“new-name = parent-package-former variational-clauses”.")
               line)

   ;; Let's not overwrite existing PackageFormers.
    (700-error (assoc $𝑛𝑎𝑚𝑒 package-formers)
               (format "PackageFormer “%s” is already defined; use a new name." $𝑛𝑎𝑚𝑒)
               line)

   ;; Ensure the PackageFormer to be instantiated is defined.
    (700-error (not self)
               (format "Parent “%s” not defined." $𝑝𝑎𝑟𝑒𝑛𝑡)
               line)

    ;; Update the new PackageFormer with a docstring of its instantiation
    ;; as well as its name.
    (setf (package-former-docstring self) line)
    (setf (package-former-name self) $𝑛𝑎𝑚𝑒)
    (setq $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠 (package-former-elements self))

    ;; Parse the “𝓋₀ ⟴ ⋯ ⟴ 𝓋ₙ” portion of an instance declaration.
     (thread-last  variations
       (s-join " ")     ;; Stick the rest back together.
       (format "'(%s)") ;; Construe as a lisp list
       read-from-string
       cadar
       (setq variations))
     ;;
     (setq alterations (𝒱𝒸 variations line))

     ;; c.f. ⁉ above
     ;; Now that the aterations have been parsed, let's attach
     ;; the new components of the PackageFormer being made.

      ;; :kind ≈ The vocabulary that replaces “PackageFormer”.
      (⁉ 'kind 'string-please)

      ;; :waist ≈ The division between parameters and remaining elements.
      (⁉ 'waist)

      ;; :waist-strings ≈ Extra strings to insert at the waist position.
      (⁉ 'waist-strings nil
          '((setq it (--map (eval it) it))))
          ;; The “eval” is since we may have Lisp that results in strings.

      ;; :level ≈ Either 'inc or 'dec, for increment or decrementing the level.
      (⁉ 'level nil ;; 'string-please
         '((let* ((lvl (package-former-level self))
                  (toLevel (lambda (n) (s-join "" (-concat
                        (-repeat n "Level.suc (") (list "Level.zero") (-repeat n ")")))))
                 (subs `("" "₁" "₂" "₃" "₄" "₅" "₆" "₇" "₈" "₉" ,(funcall toLevel 10)))
                 (here (-elem-index (s-trim lvl) subs)))

             (setq it
                   (if here

                       (pcase it
                         ('inc (nth (1+ here) subs))
                         ('dec (nth (1- here) subs)))

                     (pcase it
                       ('inc (format "Level.suc (%s)" lvl))
                       ('dec (s-join "suc" (cdr (s-split "suc" lvl :omit-nulls)))))))

             (unless it (setq it 'none)))))

      ;; :alter-elements ≈ Access the typed name constituents list.
      ;; Perform *all* element alterations, in the left-to-right ⟴ order; if any at all.
        (loop for ae in (reverse (mapcar #'cdr (--filter (equal ':alter-elements (car it)) alterations)))
              do
        (setq $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠
              (remove-duplicates (--filter (or (s-starts-with? "-- " it) it) (funcall ae $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠)) :test #'equal :from-end t)))
              ;; Filter in only the non-nil constituents & those not starting with “--” & remove duplicates.
              ;; We do this each time, rather than at the end, since variationals
              ;; may loop over all possible elements and we do not want to consider
              ;; intermediary nils or duplicates.
        (setf (package-former-elements self) $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠)

    ;; We've just formed a new PackageFormer, which can be modified, specialised, later on.
    (add-to-list 'package-formers (cons $𝑛𝑎𝑚𝑒 self))
    (when show-it (show-package-former self))))
;; Loading an Instance ---The Core Utility:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*~load-700-comments~%20and%20~lisp~%20blocks][~load-700-comments~ and ~lisp~ blocks:1]]
(defvar 700-comments nil
  "The contents of the 700-comments.

   If this variable does not change, we short-circut all processing.
   See step ‘½’ below.
  ")
;; ~load-700-comments~ and ~lisp~ blocks:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*~load-700-comments~%20and%20~lisp~%20blocks][~load-700-comments~ and ~lisp~ blocks:2]]
(cl-defun load-700-comments ()
  "Parse comments of the form “{-700 ⋯ -}” and add all PackageFormer declarations
   to the ‘package-formers’ list and all instantations to the
   ‘instantiations-remaining’ list.

   We also execute any valid Lisp code in “{-lisp -}” comments;
   which may contain an arbitrary number of Lisp forms ---a ‘progn’ is auto provided.
   Lisp is executed before any 700-comments are; which is preferable
   due to Lisp's dynamic scope.
  "
  (interactive)

  ;; First, let's run all the lisp. We enclose each in a progn in-case the user
  ;; has multiple forms in a single lisp-block.
  (loop for lispstr in (buffer-substring-delimited-whole-buffer "^\{-lisp" "^-\}")
        do (eval (car (read-from-string (format "(progn %s)" lispstr)))))

  ;; For now, ‘item’ is a PackageFormer, instantiation declaration, or other Agda code.
  (let (item lines 700-cmnts)

    ;; Catenate all 700-comments into a single string.
    (setq 700-cmnts
          (s-join "\n" (buffer-substring-delimited-whole-buffer "^\{-700" "^-\}")))

    (if (equal 700-comments 700-cmnts)

        (message "700-comments Unchanged.")

      ;; Update global.
      (setq 700-comments 700-cmnts)

      ;; View comments as a sequence of lines, ignore empty lines
      ;; ---which are not in our grammar.
      (setq lines (--remove (s-blank? (s-collapse-whitespace it)) (s-lines 700-comments)))

      ;; Traverse the 700-comments:
      ;; ➩ Skip comments; lines starting with “-- ”.
      ;; ➩ If we see a “𝒱-lhs = rhs” equation, then load it as a variational.
      ;; ➩ If we view a “lhs = rhs” equation, then load it as an instance delcaration.
      ;; ➩ If we view a PackageFormer declaration, then load it into our
      ;;   package-formers list.
      (while lines
        (setq item (car lines))

        (if (not (s-blank? (s-shared-start "-- " (s-trim item))))
            (setq lines (cdr lines))

          (if (not (s-blank? (s-shared-start "𝒱-" item)))
              (progn (load-variational item) (setq lines (cdr lines)))

            (if (s-contains? " = " item)
                (progn (load-instance-declaration item) (setq lines (cdr lines)))

              ;; Else we have a PackageFormer declaration
              ;; and other possiblly-non-700 items.
              (setq item (get-children "PackageFormer" lines))
              ;; port non-700 items to generated file
              (push (cons 'porting (s-join "\n" (car item))) package-formers)
                    ;; acknowledge PackageFormer declaration, if any
                    (when (cadr item) (load-package-former (cadr item)))
                    ;; Update lines to be the unconsidered porition
                    ;; of the wild comments.
                    (setq lines (caddr item))))))

        (message "Finished parsing 700-comments."))))
;; ~load-700-comments~ and ~lisp~ blocks:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Tooltips][Tooltips:1]]
;; Nearly instantaneous display of tooltips.
(setq tooltip-delay 0)

;; Give user 30 seconds before tooltip automatically disappears.
(setq tooltip-hide-delay 30)

(defun tooltipify (phrase notification)
  "Add a tooltip to every instance of “phrase” to show “notification”.

  Useful info on tooltips:
  http://kitchingroup.cheme.cmu.edu/blog/2013/04/12/Tool-tips-on-text-in-Emacs/
  https://www.gnu.org/software/emacs/manual/html_node/elisp/Changing-Properties.html
  http://kitchingroup.cheme.cmu.edu/blog/2016/03/16/Getting-graphical-feedback-as-tooltips-in-Emacs/
  https://stackoverflow.com/questions/293853/defining-new-tooltips-in-emacs

  The second resource above shows how to alter the phrase's font to indicate that it has
  a tooltip. It is not desirable for us, since we want to add onto Agda's coluring.
  "
  (should (stringp phrase))
  (should (stringp notification))
  (save-excursion  ;; Return cursour to current-point afterwards.
    (goto-char 1)
    (while (search-forward phrase (point-max) t)
      (put-text-property (match-beginning 0) (match-end 0) 'help-echo (s-trim notification)))))
;; Tooltips:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Advising%20our%20Beloved%20~C-c%20C-l~][Advising our Beloved ~C-c C-l~:1]]
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
       (replace-match (concat "\\1\nopen import " name-of-generated-file))))))
;; Advising our Beloved ~C-c C-l~:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Advising%20our%20Beloved%20~C-c%20C-l~][Advising our Beloved ~C-c C-l~:2]]
(defun reify-package-formers (orig-fun &rest args)
  (interactive)

  (let (generated-file-name
        printed-pfs
        (parent-imports (extract-imports)))

    ;; Sometimes we may want the full name due to files being in a nested
    ;; directory hierarchy: (file-name-sans-extension buffer-file-name)
    (setq generated-file-name
          (concat(file-name-sans-extension (buffer-name))
                 "_Generated"))

    ;; Load variationals, PackageFormers, instantiations, and porting list.
    ;; Setting the following to nil each time is not ideal.
    (setq	variationals              nil
            package-formers           nil
            700-comments              nil)

    (load-700-comments)

    (with-temp-buffer
      (beginning-of-buffer)

      ;; Copy/paste imports from parent file.
      (insert (s-join "\n" `(
         "{- This file is generated ;; do not alter. -}\n"
         ,parent-imports
         "open import Level as Level"
         ,(format "module %s where " generated-file-name)
         )))

     ;; Print the package-formers
      (setq printed-pfs
            (--map
             (if (equal 'porting (car it)) (format "%s" (cdr it))
               (format
                (if (equal "PackageFormer" (package-former-kind (cdr it)))
                    (concat "{- Kind “PackageFormer” does not correspond "
                            " to a concrete Agda type. \n%s -}")
                       "%s") (show-package-former (cdr it))))
             (reverse package-formers)))
      ;;
      (insert (s-join "\n\n\n" printed-pfs))
      ;; (setq package-formers nil) ;; So no accidental

      (write-region (beginning-of-buffer) (end-of-buffer)
                    (concat generated-file-name ".agda")))

    (insert-generated-import generated-file-name))

  ;; Need to revert buffer to discard old colours.
  ;; (save-buffer) (revert-buffer t t t)

  ;; call agda2-load
  (apply orig-fun args)

  ;; Agda attaches “jump to definition” tooltips; we add to those.
  ;; For some reason we need a slight delay between when Agda is done checking
  ;; and when we can add on our tooltips.
  ;; Attach tooltips only for existing occurrences; update happens with C-c C-l.
  (sleep-for 0.3)
  (loop for (name . pf) in package-formers
        do (unless (equal 'porting name)
             (tooltipify name (show-package-former pf))))

  ;; Let's also add tooltips for the variationals.
  (loop for (v . docs) in variationals
        do  (tooltipify (format "%s" v) docs))

  (message "700 ∷ All the best coding! (•̀ᴗ•́)و"))

; Users can enable this feature if they're interested in using it; disbale it otherwise.
; (advice-add 'agda2-load :around #'reify-package-formers)
;; Advising our Beloved ~C-c C-l~:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:1]]
(defvar 700-menu-bar (make-sparse-keymap "700 PackageFormers"))

(define-key global-map [menu-bar 700menu] (cons "700PackageFormers" 700-menu-bar))
;; Menu matter:1 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:2]]
(define-key 700-menu-bar [enable-package-formers]
  '(menu-item "Enable PackageFormer Generation" enable-package-formers))

(defun enable-package-formers ()
 (interactive)
 (advice-add 'agda2-load :around #'reify-package-formers)
 (message-box "C-c C-l now reifies “700-comments” into legitimate Agda."))
;; Menu matter:2 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:3]]
(define-key 700-menu-bar [disable-package-formers]
  '(menu-item "Disable PackageFormer Generation" disable-package-formers))

(defun disable-package-formers ()
 (interactive)
 (advice-remove 'agda2-load #'reify-package-formers)
 (setq global-mode-string (remove "700 (•̀ᴗ•́)و " global-mode-string))
  (message-box "C-c C-l now behaves as it always has."))
;; Menu matter:3 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:4]]
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
  "))
;; Menu matter:4 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:5]]
(define-key 700-menu-bar [700-bare-bones]
  '(menu-item "Copy file with 700 annotations stripped away" 700-bare-bones))

(defun 700-bare-bones ()
 (interactive)

 (let* ((src (file-name-sans-extension (buffer-name)))
        (src-agda (format "%s.agda" src))
        (bare-agda (format "%s_Bare.agda" src)))
   (with-temp-buffer
     (insert-file-contents src-agda)
     (beginning-of-buffer)
       (re-search-forward (format "module %s" src))
       (replace-match (format "module %s_Bare" src))
     (loop for pre in '("^\{-lisp" "^\{-700")
      do
      (beginning-of-buffer)
      (buffer-substring-delimited-whole-buffer pre "^-\}"
           (lambda (sp ep)
             (save-excursion
             (goto-char (- sp 2))
             (push-mark ep)
             (setq mark-active t)
             (delete-region (- sp 2) ep)))))
     (write-file bare-agda))
     (message "%s_Bare.agda has been written." src)))
;; Menu matter:5 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:6]]
(define-key 700-menu-bar [show-variationals]
  '(menu-item "Show all registered variationals" show-variationals))

(defun show-variationals ()
 (interactive)
 (occur "𝒱[ \\|-]"))

(define-key 700-menu-bar [show-pfs]
  '(menu-item "Show all concrete PackageFormers" show-pfs))

(defun show-pfs ()
 (interactive)
 (occur "PackageFormer .* where"))
;; Menu matter:6 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:7]]
(define-key 700-menu-bar [fold-700-matter]
  '(menu-item "Toggle folding away “700” and “lisp” blocks" fold-700-matter))

(defun fold-700-matter ()
 (interactive)
 (setq 700-folding (not 700-folding))
 (if 700-folding
     (message "C-c C-l will now fold away “700” and “lisp” blocks. Press ENTER to unfold a block. ")
     (fold-this-unfold-all)
     (message "Blocks “700” and “lisp” have been unfolded.")))
;; Menu matter:7 ends here

;; [[file:~/thesis-proposal/prototype/PackageFormer.org::*Menu%20matter][Menu matter:8]]
(define-minor-mode 700-mode
    "This is an editor extension prototyping “the next 700 module systems” proposed research.

    An informal documentation, with examples, page can be found at
    https://alhassy.github.io/next-700-module-systems-proposal/PackageFormer.html

    The technical matter can be found at https://alhassy.github.io/next-700-module-systems-proposal/

    If you experience anything “going wrong” or have any ideas for improvement,
    please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥
  "
  :lighter " 700 (•̀ᴗ•́)و" ;; Icon to display indicating the mode is enabled.
  :require 'foo

  ;; Toggle the menu bar
  ;; (define-key global-map [menu-bar 700menu] t)(not 700-mode))
  (define-key global-map [menu-bar 700menu] (and 700-mode (cons "700PackageFormers" 700-menu-bar)))

  (letf (( (symbol-function 'message-box) #'message))
  (if 700-mode
      ;; Initilisation
      (enable-package-formers)

      ;; Closing
      (disable-package-formers))))
;; Menu matter:8 ends here
