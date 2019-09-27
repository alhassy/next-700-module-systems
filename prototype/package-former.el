;;; package-former.el --- Making Modules with Meta-Programmed Meta-Primitives, for Agda

;; Author: Musa Al-hassy <alhassy@gmail.com>
;; Version: 1.0
;; Package-Requires: ((s "1.12.0") (dash "2.16.0") (origami "1.0")  (emacs "24.4"))
;; Keywords: agda, modules, packages, theories, languages, convenience, maint, tools
;; URL: https://alhassy.github.io/next-700-module-systems

;; Copyright (c) 2019 Musa Al-hassy

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This program is intended to reduce the burden in selecting
;; the form of records and other kinds of packages in Agda.
;; For example, the decision of whether a record element should be
;; declared as a field or as a parameter no longer needs to be performed
;; prematurely but rather may be selected when necessary.

;; This el file has been tangled from a literate, org-mode, file.
;; See the documentation on:
;; https://alhassy.github.io/next-700-module-systems/prototype/package-former.html

;;; Code:

;; String and list manipulation libraries
;; https://github.com/magnars/dash.el
;; https://github.com/magnars/s.el
(require 's)               ;; “The long lost Emacs string manipulation library”
(require 'dash)            ;; “A modern list library for Emacs”
(require 'dash-functional) ;; Function library; ‘-const’, ‘-compose’, ‘-orfn’, ‘-not’, ‘-partial’, etc.
(require 'origami)         ;; Folding away regions of text
(require 'subr-x)          ;; Extra Lisp functions; e.g., ‘when-let’.
(require 'ert)             ;; Testing framework; ‘should’ for assertions

;; Crashes if an argument is ":"
(cl-defmacro pf--declare-type (f key-types &rest types)
  "Attach the given list of types to the function ‘f’
   by advising the function to check its arguments’ types
   are equal to the list of given types.

   We name the advice ‘⟪f⟫-typing-advice’ so that further
   invocations to this macro overwrite the same advice function
   rather than introducing additional, unintended, constraints.

   Using type specifiers we accommodate for unions of types
   and subtypes, etc ♥‿♥.

   ‘key-types’ should be of the shape (:x₀ t₀ ⋯ :xₙ tₙ);
    when there are no optional types, use symbol “:”.

    E.g., (pf--declare-type my-func (:z string :w integer) integer symbol string)
  "

  ;; Basic coherency checks. When there aren't optional types, key-types is the “:” symbol.
  (should (and (listp types) (or (listp key-types) (symbolp key-types))))

  (letf* ((pairify (lambda (xs) (loop for i in xs by #'cddr         ;; Turn a list of flattenned pairs
                                      for j in (cdr xs) by #'cddr   ;; into a list of explicit pairs.
                                      collect (cons i j))))         ;; MA: No Lisp method for this!?
         (result-type  (car (-take-last 1 types)))
         (types        (-drop-last 1 types))
         (num-of-types (length types))
         (key-types-og (unless (symbolp key-types) key-types))
         (key-types    (funcall pairify key-types-og))
         (advice-name  (intern (format "%s-typing-advice" f)))
         (notify-user  (format "%s now typed %s → %s → %s."
                               `,f key-types-og types result-type)))

      `(progn
         (defun ,advice-name (orig-fun &rest args)

           ;; Split into positional and key args; optionals not yet considered.
           (letf* ((all-args
                     (-split-at
                       (or (--find-index (not (s-blank? (s-shared-start ":" (format "%s" it)))) args) ,num-of-types)
                        args)) ;; The “or” is for when there are no keywords provided.
                  (pos-args  (car all-args))
                  (key-args  (funcall ,pairify (cadr all-args)))
                  (fun-result nil)
                  ((symbol-function 'shucks)
                     (lambda (eτ e g)
                       (unless (typep g eτ)
                         (error "%s: Type mismatch! Expected %s %s ≠ Given %s %s."
                                (function ,f) eτ e (type-of g) (prin1-to-string g))))))

         ;; Check the types of positional arguments.
         (unless (equal ,num-of-types (length pos-args))
           (error "%s: Insufficient number of arguments; given %s, %s, but %s are needed."
                  (function ,f) (length pos-args) pos-args ,num-of-types))
         (loop for (ar ty pos) in (-zip pos-args (quote ,types) (number-sequence 0 ,num-of-types))
               do (shucks ty (format "for argument %s" pos) ar))

         ;; Check the types of *present* keys.
         (loop for (k . v) in key-args
               do (shucks (cdr (assoc k (quote ,key-types))) k v))

         ;; Actually execute the orginal function on the provided arguments.
         (setq fun-result (apply orig-fun args))
         (shucks (quote ,result-type) "for the result type (!)" fun-result)

         ;; Return-value should be given to caller.
         fun-result))

      ;; Register the typing advice and notify user of what was added.
      (advice-add (function ,f) :around (function ,advice-name))
      ,notify-user )))

;; (pf--declare-type pf--get-indentation : string integer)
(defun pf--get-indentation (string)
  "How many spaces are there at the front of ‘string’?

  Property: The resulting number is ‘≤ length string’.
  "
  (if string (length (s-shared-start string (s-repeat (length string) " "))) 0))

(pf--declare-type get-children (:then t) string (or string list) cons)
(cl-defun pf--get-children (parent the-wild &key (then #'identity))
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
        unconsidered
        prefix
        lines&more
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
    (setq indentation (pf--get-indentation (car lines)))

    ;; Keep only the children that have at least this level of indentation.
    (setq lines&more (--split-with (<= indentation (pf--get-indentation it)) lines))
    (setq lines (car lines&more))
    (setq unconsidered (cadr lines&more))

    ;; Alter the children according to the given function.
    (setq lines (mapcar then lines))

    ;; Yield the parent line along with the children lines; and the unconsumed wild's prefix and suffix.
    `(,prefix ,(cons parent-line lines) ,unconsidered)))

;; This may accept argument ":", which “pf--declare-type” cannot currently handle.
(cl-defun pf--substring-delimited
    (prefix suffix string)
  "Assuming ‘string’ ≈ ⋯‘prefix’⟪needle⟫‘suffix’⋯, return the /first/ such needle.

    NOTE: Delimiters ‘prefix’ and ‘suffix’ may be empty.

  We convert all adjacent whitespace
  characters to a single space in the input ‘string’ and trim any surrounding
  whitespace from the resulting output needle string.
  "

  (unless (stringp string) (error "pf--substring-delimited: Argument ‘string’ must be a string."))
  (let* ((new (s-collapse-whitespace string)))

  (when (not (s-blank? prefix))
    (setq new (car (-take-last (if (equal prefix suffix) 2 1) (s-split prefix new)))))

  (when (not (s-blank? suffix))
    (setq new (car (s-split suffix new))))

  (s-trim new)))

;; This may accept argument ":", which “pf--declare-type” cannot currently handle.
(cl-defun pf--substring-delimited-here (context string)
  "Assuming ‘context’ = “⟪prefix⟫ $here ⟪suffix⟫”
   and ‘string’ ≈ ⋯‘prefix’⟪needle⟫‘suffix’⋯, return the /first/ such needle.

  NOTE: ⟪prefix⟫ and ⟪suffix⟫ cannot be empty strings!

  We convert all adjacent whitespace
  characters to a single space in the input ‘string’ and trim any surrounding
  whitespace from the resulting output needle string.
  "

  (-let [pre-post (s-split "$here" context)]
    (pf--substring-delimited (s-trim (car pre-post)) (s-trim (cadr pre-post)) string)))

;; pf--declare-type has no support for optionals yet
(cl-defun pf--buffer-substring-delimited (start end &optional more &key (regexp t))
  "
  Get the current buffer's /next/ available substring that is delimited
  between the regexp tokens ‘start’ up to ‘end’, exclusively.

  If no tokens are found, an error is thrown.

  ‘more’ is a function that is called on the found instance:
  It is a function of the start and end positions of the occurance.

  ‘regexp’ indicates whether we are using regular expression strings, or literals.
   It is ‘nil’ by default.
  "
  (let (start-pos end-pos sp ep content)
    (if regexp (re-search-forward start) (search-forward start))
    (setq start-pos (point))
    (backward-word)
    (setq sp (point))

    (if regexp (re-search-forward end) (search-forward end))
    (setq ep (point))
    (backward-word)
    (setq end-pos (point))

    (setq content  (buffer-substring-no-properties start-pos end-pos))

    (when more (funcall more sp ep))
    (when pf-folding (origami-close-node-recursively (current-buffer) (point)))

    content))

(defvar pf-folding nil
  "Should 700 and lisp blocks be folded away when C-c C-l.")

;; pf--declare-type has no support for optionals yet
(cl-defun pf--buffer-substring-delimited-whole-buffer (start end &optional more)
  "Return a list of all substrings in the current buffer that
   are delimited by regexp tokens ‘start’ and ‘end’, exclusively.

  ‘more’ is a function that is called on the found instance:
  It is a function of the start and end positions of the occurance.
  "
  ;; Colour 700 keywords red “'error”
  (highlight-phrase start 'error)
  (highlight-phrase end 'error)
  (save-excursion
    (let ((l nil) (continue t))
     (beginning-of-buffer)

     (while continue
       (condition-case nil
     ;; attemptClause
     (setq l (cons (pf--buffer-substring-delimited start end more) l))
     ;; recoveryBody
     (error (setq continue nil))))

     ;; We've collected items as we saw them, so ‘l’ is in reverse.
    (reverse l))))

(defun rename-mixfix (f op &optional avoid-mixfix-renaming)
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

   AVOID-MIXFIX-RENAMING is optional; by default renaming “jumps over” underscores,
   but providing a non-nil value for this argument leaves underscores alone.
   It is a matter of having, say, default “_⊕ₙ_” versus “_⊕_ₙ”.
  "

  (let* ((parts (s-split "_" op)) (front (s-blank? (first parts))) (rear (s-blank? (car (last parts)))))

    (if avoid-mixfix-renaming
        (funcall f op)
      (--> (concat (when front "_") "$here" (when rear "_"))
           (pf--substring-delimited-here it op)
           (funcall f it)
           (concat (when front "_") it (when rear "_"))))))

(defvar pf-generated-suffix "-generated"
  "The suffix applied to a file's name to produce it's generated counterpart.")

;; Sometimes we may want the full name due to files being in a nested
;; directory hierarchy: (file-name-sans-extension buffer-file-name)
(defun pf--generated-file-name ()
  "Name of the generated file."
  (concat (file-name-sans-extension (buffer-name)) pf-generated-suffix))

(pf--declare-type extract-imports : string)
(cl-defun pf--extract-imports ()
  "Return substring of buffer whose lines mention “import”.
   Throw away any that mention the substring “⟪FileName⟫_Generated”.
  "
  (thread-last (buffer-substring-no-properties (point-min) (point-max))
    (s-split "\n")
    (--filter (s-contains? "import " it))
    (--remove (s-contains? (pf--generated-file-name) it))
    (s-join "\n")))

(defmacro λ (&rest body)
  "Implementing Agda style, interactive, lambdas; ideally for inline use:

   “λ α β … ω → body”  becomes an interactive function with arguments α, …, ω.

   The args list may be empty, in which case the separator “→” may be omitted
   entirely, if desired.
  "

  (let* ((parts (-split-on '→ body)) args rest)

    (if (<= 2 (length parts))
        (progn (setq args (car parts)) (setq rest (cadr parts)))
         ;; Otherwise, only one part was found ---no arguments were provided.
         (setq args nil) (setq rest (car parts)))

   `(lambda ,args (interactive) ,@rest)
  ))

(defstruct pf--package-former
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

   TODO: Eventually need to support variations?
  "
  docstring
  kind
  name
  level

  waist ;; Delimits elements into parameters and fields.

  ;; children
  indentation ;; useful for when new elements are added.
  elements
)

(defvar pf--package-formers nil
  "The list of PackageFormer schema declarations in the current Agda buffer.")

;; An anaphoric macro ^_^
(defmacro pf--open-pf (p &rest body)
  "Open a package-former so no qualiiers are required."
  `(let*
    ((docstring             (pf--package-former-docstring ,p))
     (kind                  (pf--package-former-kind ,p))
     (name                  (pf--package-former-name ,p))
     (level                 (pf--package-former-level ,p))
     (waist                 (pf--package-former-waist ,p))
     (indentation           (pf--package-former-indentation ,p))
     (elements              (pf--package-former-elements ,p))

    ;; ‼ TODO: MA: Eventually need to support variations?

    (parameters            (-take waist elements))
    (fields                (-drop waist elements)))
    ,@body
  )
)

(defstruct element

  qualifier ;; E.g., “private, field”
  name      ;; The lhs of an equation and a typed-name
  type      ;; The type of a typed-name
  equations ;; List of definitional clauses: “same-name-as-above args = term”
)

(loop for place in '(qualifier name type equations)
      do
      (-let [loc (intern (format "element-%s" place))]
        (eval `(defun ,(intern (format "map-%s" place)) (f e)
           "??? TODO:"
           (-let [e′ (copy-element e)]
             (setf (,loc e′) (funcall f (,loc e′)))
             e′)))))

(defun element-replace (old new e)
  "Replace every occurance of /word/ ‘old’ by string ‘new’
   in element ‘e’."

  (-let [e′ (copy-element e)]
    (loop for place in '(element-qualifier element-name element-type)
          do (eval `(setf (,place e′)
                          (replace-regexp-in-string (format "\\b%s\\b" old)
                                                    new (,place e′) t t))))
    ;; Replacements in the equations as well.
    (setf (element-equations e′)
          (loop for eq in (element-equations e′)
                collect (s-replace old new eq)))
    ;; return value
    e′))

(pf--declare-type parse-name : string string)
(defun parse-name (element)
  "Given an string representation of an ‘element’, yield the ‘name’ component.

   The shape of the input may be “qualifier lhs ~ rhs” where ‘~’ is either ‘:’
   or ‘=’. The qualifier is a ‘special’ word: field, private.
  "
  (let (lhs name)
    (setq lhs
          (s-split " " (car (s-split " = " (car (s-split " : " element))))))
    (if (and (< 1 (length lhs)) (pf--special (nth 0 lhs)))
        (cadr lhs)
      (car lhs))))

(pf--declare-type parse-elements : (list-of string) (list-of element))
(defun parse-elements (elements)
  "Given a list of PackageFormer ‘elements’, as strings, parse them into the
  ‘element’ datatype. Declarations and equations may be interspersed, as along
  as equations of names follow their declarations.

   The order is preserved in-case there are declarations that make use of definitions.

   Types must always be supplied ---in general, type inference is undecidable in DTLs.
   "

  (-let [es (mapcar #'list elements)]
    ;; Maintain a list of related items.
    (loop for i from 0
          for e in es
          do
          (loop for j from 0 to (1- i)
                do
                ;; If the name of ‘e’ occurs in the prefix,
                ;; then move ‘e’ to the location in the prefix,
              ;; and zero-out the current location.
              (let (lhs name)
                 (setq name (parse-name (car e)))

                 (when (equal name (parse-name (or (car (nth j es)) "")))
                   ;; Use an empty string in-case the location is nil.
                   (setf (nth j es) (append (nth j es) e))
                   (setf (nth i es) nil)))))

    ;; Drop the nils.
    (setq es (--reject (not it) es))

    ;; We now have a list of related items,
    ;; with the car of each being a qualified typed-name
    ;; and the cdr of each being a list of equational clauses associated with that name.
    (loop for e in es
          collect
          (let* ((τ (s-split " : " (car e)))
                 (nom (parse-name (car τ)))
                 (qual (car (s-split nom (car τ)))))
            (make-element :qualifier (unless (s-blank? qual) qual)
                          :name nom
                          :type (if (cdr τ) (s-join " : " (cdr τ))
                                  (error (message-box
                                          "Error: Type not supplied for %s!" nom)))
                          :equations (cdr e))))))

; (pf--declare-type pf--load-package-former : (list-of string) package-former)
(pf--declare-type pf--load-package-former : t t)
(defun pf--load-package-former (lines)
  "The input ‘lines’ must be a list of lines forming a full PackageFormer declaration;
   e.g., obtained by calling ‘pf--get-children’.

   It is parsed and a ‘package-former’ value is returned.

   - Whitespace is stripped off of items.
   - Docstrings are ignored.
  "

  (when (not lines)
      (error "pf--load-package-former: Error: Input must be non-empty list."))

  (let* (pf
         (header (or (car lines) ""))
         (name (pf--substring-delimited-here "PackageFormer $here :" header))
         (level (pf--substring-delimited-here "Set $here where" header)))

    (when pf-highlighting
      (--map (highlight-phrase (s-trim it) 'hi-yellow) (cdr lines)))

    (setq pf
          (make-pf--package-former
           :kind                     "PackageFormer"
           :name                     name
           ;; ‘level’ may be “”, that's okay.
           ;; It may be a subscript or implicitly zero & so no space after ‘Set’.
           :level                    level
           :waist                    0
           ;; ‼ TODO: Currently no parameter support for arbitrary PackageFormers.
           :indentation              (pf--get-indentation (cadr lines))
           :elements  (parse-elements (--remove (s-starts-with? "-- " it)
                                                (--map (s-trim it) (cdr lines))))))

      (push (cons name pf) pf--package-formers)

      ;; return value
      pf))

(pf--declare-type special : string t)
(defun pf--special (f)
  "Special elements, for whatever reason are exceptional, and so
   are maked as singleton lists and their indentation is lessened.
   That is, these denote sibling fields rather than more children.

   Special elements include: field, private.

   See ‘show-package-former’ for their use and how their printed.
  "
  (--any? (s-contains? it f) '("field" "private" "open" "top-level" "sibling")))

(pf--declare-type show-element (:omit-qualifier t) element string)
(cl-defun show-element (e &optional omit-qualifier)
  "Render an ‘element’ value in the form

       qualifier name : type ; equational-clause₀ ; ⋯ ; equational-clauseₙ
  "

  (s-join " ;\t" (cons
                 (format "%s%s\t\t: %s"
                         (-let [it (element-qualifier e)] (if (or (not it) omit-qualifier) "" (format "%s " it)))
                         (element-name e)
                         (element-type e))
                 (element-equations e))))

(pf--declare-type pf--show-package-former : pf--package-former string)
(cl-defun pf--show-package-former (p)
  "Pretty print a package-former record value.
  "

  (pf--open-pf p
    (s-join "\n"
      (-cons*

       ;; The documentation string
       (when docstring (format "{- %s -}" docstring))

       ;; The schema declaration
       (s-collapse-whitespace
        (s-join " "
                (list kind
                      name
                      (s-join " " (--map (concat "(" (show-element it :omit-qualifier) ")") parameters))
                      (unless (equal level 'none) (concat ": Set" level))
                      "where")))

       ;; The elements of a PackageFormer
       (thread-last fields
         (--map (format "%s%s" (s-repeat indentation " ") (show-element it)))
         )
       ))))

         ;; Indent all elements, less indentation for the specials.
         ;; Regarding “top-level” see the “recordₑ” variational in Paper0.pdf.
         ;; The extra whitespace is important.
         ;; (--map (concat (s-repeat (- indentation (if (pf--special it) 2 0)) (if (s-starts-with? "sibling" it) "" " "))
         ;;                (if (s-starts-with? "top-level" it) (s-chop-prefix "top-level " it)
         ;;                 (if (s-starts-with? "sibling" it) (s-chop-prefix "sibling " it) it))))

(setq pf--variationals nil)
;;  "Association list of Agda-user defined variational operators."

(defvar pf-variational-composition-operator "⟴"
  "The operator that composes varitionals.")

(when nil *parent-context* nil
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
     (cl-defun 𝒱-test (&key height kind) (list (format \"%s & %s\" height kind)))
     (𝒱𝒸 '(test :height 3 :kind 'data)) ≈ (test :height 3 :kind data) ≈ (“3 & data”)
     (𝒱𝒸 '(     :height 3 :kind data))  ≈ ((:height . 3) (:kind . data))

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
                            (progn
                              ;; The variational being called is defined.
                              (pf--ensure (fboundp (𝒱- (car clause)))
                                        (format "Did you mistype a variational's name: “%s” is not defined." (car clause))
                                        context
                                        "Use the PackageFormer menu to see which variationals are defined.")
                              (eval `( ,(𝒱- (car clause)) ,@(cdr clause))))
                          ;; List of key-value pairs
                          `,(loop for key   in clause by #'cddr
                                  for value in (cdr clause) by #'cddr
                                  collect (pf--wf key value context args)))  ;; “pf--wf” is just a fancy “cons”.
                        ;; Newer items c₀ ⟴ ⋯ ⟴ cₙ should be at the front of the list;
                        ;; access should then be using assoc.
                        res)))
    res))

(defun 𝒱- (name)
  "Prefix the Lisp data ‘name’ with a “𝒱-”
   then yield that as a Lisp datum.
  "
  (should (symbolp name))
  (thread-last name
    (format "𝒱-%s")
    read-from-string
    car))

(defmacro 𝒱 (name &rest body)

  "Reify as Lisp a variational declaration using the following grammar.

        𝓋   ::= [docstring] identifier ([“(”]identifier[“)”])* = 𝓋𝒸
        𝓋𝒸  ::= [identifier] (:key value)* (⟴ 𝓋𝒸)*

    E.g., (𝒱 tes positional (keyword 3) = :kind data)
    This defines a variational with one positional and one keyword argument having
    3 as default.

    The resulting generated function has its code embeded as a docstring viewable
    with “C-h o” ---catented after any provided user documentation.
  "

  ;; Main code follows.
  (let* ((context (mapconcat (lambda (x) (prin1-to-string x t)) (cons name body) " "))
         (args-body (-split-on '= body)) args pargs kargs argnames docs body res actual-code)
    (pcase (length args-body)
      (2 (setq args (car args-body)
               body (cadr args-body)))
      (t (setq body (car args-body))))

    ;; Realise the arguments as either 𝒫ositinal or 𝒦ey arguments.
    (loop for a in args
          do (if (consp a) (push a kargs) (push a pargs)))

    ;; The arguments are in reverse now, which doesn't matter for keywords
    ;; yet is crucial for positional arguments. So let's fix that.
    (setq pargs (reverse pargs))

    ;; Keep track of only the argument names, omitting any default values.
    (setq argnames (append pargs (mapcar #'car kargs)))

    ;; Set any documentation string and reify the body's variational clauses.
    (when (stringp (car body)) (setq docs (car body) body (cdr body)))
    (setq res (𝒱𝒸 body context argnames))

    ;; I want to be able to actually, visually, see the resulting
    ;; generated definition of a function.
    ;; Hence, I embed its source code as a string in the code.
    ;;
    ;; I'm using strings so that they appear in the docstring via C-h o.
    ;;
    (setq actual-code
    `(cl-defun ,(𝒱- name) (,@pargs &key ,@kargs)

       ;; Stage the formal names *now*, then evaluate their values at run time.
       ;; Traverse the list of pairs and change the nested formal names with the
       ;; given values. Praise the Lord!
      (let* ((give-goal (quote ,res)) (give-goal₀ give-goal))
        (when (quote ,argnames)

          "Stage the formal names *now*, then evaluate their values at run time."
          (loop for arg in (quote ,argnames)
                do (setq give-goal (subst (eval arg) arg give-goal)))

          ;; TODO, maybe.
          ;; "Check that substituted values are well-typed"
          ;; (--map (pf--wf (car it) (or (cdr it)
          ;;                             ;; Mention which argument is not supplied.
          ;;                             (format "No Value for :%s Provided!"
          ;;                                     (cdr (assoc (car it) (reverse give-goal₀)))))
          ;;                (s-concat (when *parent-context* (s-concat *parent-context* "\n\t➩\t")) ,context)) give-goal)

          )

         give-goal)))

    ;; Now set the code as a documentation string in it, after the fact.
    (setq docs (format "Arguments:\t%s %s\n%s" pargs (reverse kargs)
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
    (push (cons name docs) pf--variationals)
    ;; Return value:
    actual-code))

(defmacro pf--ensure (condition message context &rest suggestions)
  "Ensure ‘condition’ is true and defined, otherwise emit ‘message’
   and indicate the offending ‘context’.
   If there are any ‘suggestions’ to the user, then we show those too.

   ➩ If ‘condition’ is defined and non-nil, whence true, we return it.
  "
  `(let* ((ლ\(ಠ益ಠ\)ლ
          (format "700: %s\n\n\t⇨\t%s%s%s" ,message ,context
                  (if (quote ,suggestions) "\n" "")
                  (s-join "\n" (--map (format "\t⇨\t%s" it) (quote ,suggestions)))))
         ;; Try to evaluate the condition.
         (res (condition-case nil ,condition (error ლ\(ಠ益ಠ\)ლ))))

    ;; If we've made it here, then the condition is defined.
    ;; It remains to check that it's true.
    (or res (error ლ\(ಠ益ಠ\)ლ))))

;; pf--declare-type cannot yet accomodate optional arguments
(cl-defun pf--wf (key value &optional context args)
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
                (:level (-contains? '(inc dec none) value) (format "The “level” must be “inc” or “dec” or “none”; which “%s” is not." value))
                ; (:alter-elements (functionp value) (format "Componenet alter-elements should be a function; which “%s” is not." value))
                       )))

    (when-let ((here (assoc key wf)))
      (setq condition        (eval (nth 1 here))
            message          (eval (nth 2 here)))
      (pf--ensure (or condition (-contains? args value)) message context))

    ;; Return the key-value as a pair for further processing.
    ;; :kind and :level values are symbols and so cannot be evaluated furthur.
    (cons key
          (if
           (or (-contains? args value) (-contains? '(:kind :level) key))
           value
           (eval value)))))

(cl-defun pf--load-variational (variation-string)
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

(defstruct pf-instance-declaration
  "Record of components for an PackageFormer instance declaration:
   ⟪name⟫ = ⟪package-former⟫ (⟴ ⟪variation⟫ [⟪args⟫])*
  "

  docstring      ;; What the declaration looks like, useful for reference.
  name           ;; Left-hand side
  package-former ;; Parent grouping mechanism
  alterations    ;; List of variationals along with their arguments.
)

(defun pf--load-instance-declaration (line &optional show-it)
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
     (self (copy-pf--package-former (cdr (assoc $𝑝𝑎𝑟𝑒𝑛𝑡 pf--package-formers))))
     ((symbol-function '⁉)
      ;; If componenet ‘c’ is in the ‘alterations’ list of the instance declaration,
      ;; then evalaute any given ‘more’ code, get the value for ‘c’ and turn it
      ;; into a string, if ‘str’ is true, then set the new PackageFormer's ‘c’
      ;; componenet to be this value.
      ;; Well-formedness checks happen at the 𝒱 and 𝒱𝒸 stages, see below.
         (lambda (c &optional str more) (when-let ((it (cdr (assoc (intern (format ":%s" c)) alterations))))
                           (eval `(progn ,@more))
                           (when str (setq it (format "%s" it)))
                           (eval `(setf (,(car (read-from-string (format "pf--package-former-%s" c))) self) it))))))

   ;; Ensure instance declaration is well-formed.
    (pf--ensure (and (not (s-blank? (s-trim $𝑛𝑎𝑚𝑒))) (equal "=" eqSymb) $𝑝𝑎𝑟𝑒𝑛𝑡)
               (concat "An instance declaration is of the form "
                       "“new-name = parent-package-former variational-clauses”.")
               line)

   ;; Let's not overwrite existing PackageFormers.
    (pf--ensure (not (assoc $𝑛𝑎𝑚𝑒 pf--package-formers))
               (format "PackageFormer “%s” is already defined; use a new name." $𝑛𝑎𝑚𝑒)
               line)

   ;; Ensure the PackageFormer to be instantiated is defined.
    (pf--ensure self
               (format "Parent “%s” not defined." $𝑝𝑎𝑟𝑒𝑛𝑡)
               line)

    ;; Update the new PackageFormer with a docstring of its instantiation
    ;; as well as its name.
    (setf (pf--package-former-docstring self) line)
    (setf (pf--package-former-name self) $𝑛𝑎𝑚𝑒)
    (setq $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠 ; Copy so that user does not inadvertently alter shared memory locations!
          (loop for e in (pf--package-former-elements self)
                 collect (copy-element e)))

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

      ;; :level ≈ Either 'inc or 'dec, for increment or decrementing the level.
      (⁉ 'level nil ;; 'string-please
         '((let* ((lvl (pf--package-former-level self))
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
              (remove-duplicates (--filter it (funcall ae $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠)) :test #'equal :from-end t)))
              ;; Filter in only the non-nil constituents & those not starting with “--” & remove duplicates.
              ;; We do this each time, rather than at the end, since variationals
              ;; may loop over all possible elements and we do not want to consider
              ;; intermediary nils or duplicates.
        (setf (pf--package-former-elements self) $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠)

    ;; We've just formed a new PackageFormer, which can be modified, specialised, later on.
    (add-to-list 'pf--package-formers (cons $𝑛𝑎𝑚𝑒 self))
    (when show-it (pf--show-package-former self))))

(defvar pf--annotations nil
  "The contents of the pf--annotations.

   If this variable does not change, we short-circut all processing.
  ")

;; ("^\\\\begin{lisp}" . "^\\\\end{lisp}"))

(cl-defun pf--load-pf--annotations ()
  "Parse comments of the form “{-700 ⋯ -}” and add all PackageFormer declarations
   to the ‘package-formers’ list and all instantations to the
   ‘instantiations-remaining’ list.

   We also execute any valid Lisp code in “{-lisp -}” comments;
   which may contain an arbitrary number of Lisp forms ---a ‘progn’ is auto provided.
   Lisp is executed before any pf--annotations are; which is preferable
   due to Lisp's dynamic scope.
  "
  (interactive)

  ;; First, let's run all the lisp. We enclose each in a progn in-case the user
  ;; has multiple forms in a single lisp-block.
  (loop for (lispstart . lispend) in '(("^\{-lisp" . "^-\}"))
        do (loop for lispstr in (pf--buffer-substring-delimited-whole-buffer lispstart lispend)
                 do (eval (car (read-from-string (format "(progn %s)" lispstr))))))

  ;; For now, ‘item’ is a PackageFormer, instantiation declaration, or other Agda code.
  (let (item lines 700-cmnts)

    ;; Catenate all pf--annotations into a single string.
    (setq 700-cmnts
          (s-join "\n" (pf--buffer-substring-delimited-whole-buffer "^\{-700" "^-\}")))
    ;; (setq 700-cmnts (append 700-cmnts
    ;;                         (s-join "\n" (pf--buffer-substring-delimited-whole-buffer "700}" "end"))))

    (if (equal pf--annotations 700-cmnts)

        (message "pf--annotations Unchanged.")

      ;; Update global.
      (setq pf--annotations 700-cmnts)

      ;; View comments as a sequence of lines, ignore empty lines
      ;; ---which are not in our grammar.
      (setq lines (--remove (s-blank? (s-collapse-whitespace it)) (s-lines pf--annotations)))

      ;; Traverse the pf--annotations:
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
              (progn (pf--load-variational item) (setq lines (cdr lines)))

            (if (s-contains? " = " item)
                (progn (pf--load-instance-declaration item) (setq lines (cdr lines)))

              ;; Else we have a PackageFormer declaration
              ;; and other possiblly-non-700 items.
              (setq item (pf--get-children "PackageFormer" lines))
              ;; port non-700 items to generated file
              (push (cons 'porting (s-join "\n" (car item))) pf--package-formers)
                    ;; acknowledge PackageFormer declaration, if any
                    (when (cadr item) (pf--load-package-former (cadr item)))
                    ;; Update lines to be the unconsidered porition
                    ;; of the wild comments.
                    (setq lines (caddr item))))))

        (message "Finished parsing pf--annotations."))))

(defvar pf-highlighting t
  "Should PackageFormer syntactical items be coloured?

   ➩ Yellow for PackageFormer content.
   ➩ Red for delimiters “700” and “lisp”.
   ➩ Green for names of variationals.
  ")

;; Nearly instantaneous display of tooltips.
(setq tooltip-delay 0)

;; Give user 30 seconds before tooltip automatically disappears.
(setq tooltip-hide-delay 30)

(defun pf--tooltipify (phrase notification)
  "Add a tooltip to every instance of “phrase” to show “notification”.

   We only add tooltips to “phrase” as a standalone word, not as a subword.

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
    ;; The \b are for empty-string at the start or end of a word.
    (while (search-forward-regexp (format "\\b%s\\b" phrase) (point-max) t)
      (put-text-property (match-beginning 0) (match-end 0) 'help-echo (s-trim notification)))))

(defun pf--insert-generated-import (name-of-generated-file)
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

(defvar pf-waiting-for-agda-threshhold 14
    "How long we should wait for Agda before giving up on colouring and tooltips.

     Default is to wait 4 × 0.5 milliseconds.

     Why? An inital agda2-load of a ~300 line file may take some time.
    ")

(defun pf--reify-package-formers (orig-fun &rest args)
  "Parse package-former syntax and produce Agda when possible."
  (interactive)
  (let* (printed-pfs
        (parent-dir (s-join "/" (-drop-last 1 (s-split "/" buffer-file-truename))))
        (generatedmodule  (pf--generated-file-name))
        (newfile (concat parent-dir "/" generatedmodule ".agda"))
        (parent-imports (pf--extract-imports)))

    ;; Load variationals, PackageFormers, instantiations, and porting list.
    ;; Setting the following to nil each time is not ideal.
    (setq	pf--variationals (-take-last ♯standard-variationals pf--variationals) ;; take last n items, those being exported into the .el.
            pf--package-formers       nil
            pf--annotations           nil)

    (pf--load-pf--annotations)

    (with-temp-buffer
      (beginning-of-buffer)

      ;; Copy/paste imports from parent file.
      (insert (s-join "\n" `(
         "{- This file is generated ;; do not alter. -}\n"
         ,parent-imports
         "open import Level as Level"
         ,(format "module %s where " generatedmodule))))

     ;; Print the package-formers
      (setq printed-pfs
            (--map
             (if (equal 'porting (car it)) (format "%s" (cdr it))
               (format
                (if (equal "PackageFormer" (pf--package-former-kind (cdr it)))
                    (concat "{- Kind “PackageFormer” does not correspond "
                            " to a concrete Agda type. \n%s -}")
                       "%s") (pf--show-package-former (cdr it))))
             (reverse pf--package-formers)))
      ;;
      (insert (s-join "\n\n\n" printed-pfs))
      ;; (setq package-formers nil) ;; So no accidental

      ;; Replace tabs with spaces
      (untabify (point-min) (point-max))

      (write-region (beginning-of-buffer) (end-of-buffer) newfile))

    (pf--insert-generated-import generatedmodule)

  ;; Need to revert buffer to discard old colours.
  ;; (save-buffer) (revert-buffer t t t)

  ;; call agda2-load
  (apply orig-fun args)

  ;; Agda attaches “jump to definition” tooltips; we add to those.
  ;; For some reason we need a slight delay between when Agda is done checking
  ;; and when we can add on our tooltips.
  ;; Attach tooltips only for existing occurrences; update happens with C-c C-l.
  ;; Wait until Agda is finished highlighting, then do ours (งಠ_ಠ)ง
  (-let [counter 0] ; agda2-in-progress
    (while agda2-highlight-in-progress
      (when (> counter pf-waiting-for-agda-threshhold) (error "PackageFormer ∷ Items generated, but not coloured; Agda seems busy..."))
      (incf counter)
      (sleep-for 0.5))) ;; In case Agda errors on a term, no more waiting.
  (loop for (name . pf) in pf--package-formers
        do (unless (equal 'porting name)
             (pf--tooltipify name (pf--show-package-former pf))))

  ;; Let's also add tooltips for the variationals & colour them.
  (loop for (v . docs) in pf--variationals
        do (pf--tooltipify (format "%s" v) docs)
        ;; For beauty, let's colour variational names green.
        ;; Only colour occurances that have a space before or after.
        (when pf-highlighting
          (highlight-phrase (format "[- \\| ]%s " v) 'hi-green)))

  (message "PackageFormer ∷ All the best coding! (•̀ᴗ•́)و")))

; Users can enable this feature if they're interested in using it; disbale it otherwise.
; (advice-add 'agda2-load :around #'pf--reify-package-formers)

(defvar pf--menu-bar (make-sparse-keymap "PackageFormer"))

(define-key pf--menu-bar [pf-enable-package-formers]
  '(menu-item "Enable PackageFormer Generation" pf-enable-package-formers))

(defun pf-enable-package-formers ()
 "Add a menubar, and make Agda's C-c C-l consider package-former syntax."
 (interactive)
 (define-key global-map [menu-bar pf--menu] (cons "PackageFormer" pf--menu-bar))
 (advice-add 'agda2-load :around #'pf--reify-package-formers)
 (message-box "C-c C-l now reifies PackageFormer annotations into legitimate Agda."))

(define-key pf--menu-bar [pf-disable-package-formers]
  '(menu-item "Disable PackageFormer Generation" pf-disable-package-formers))

(defun pf-disable-package-formers ()
  "Remove menubar, and make Agda's C-c C-l act as normal."
 (interactive)
 (define-key global-map [menu-bar pf--menu] nil)
 (advice-remove 'agda2-load #'pf--reify-package-formers)
 (setq global-mode-string (remove "PackageFormer (•̀ᴗ•́)و " global-mode-string))
  (message-box "C-c C-l now behaves as it always has."))

(define-key pf--menu-bar [pf-package-formers-about]
  '(menu-item "About PackageFormers" pf-package-formers-about))

(defun pf-package-formers-about ()
  "Show help about the PackageFormer system."
 (interactive)
 (switch-to-buffer "*PackageFormer-About*") (insert
  " This is an editor extension prototyping “the next 700 module systems” proposed research.

    An informal documentation, with examples, page can be found at
    https://alhassy.github.io/next-700-module-systems/prototype/package-former.html

    The technical matter can be found at https://alhassy.github.io/next-700-module-systems/

    If you experience anything “going wrong” or have any ideas for improvement,
    please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥
  "))

(define-key pf--menu-bar [pf--bare-bones]
  '(menu-item "Copy file with PackageFormer annotations stripped away" pf--bare-bones))

(defun pf-bare-bones ()
  "Produce a copy of the current file with PackageFormer annotations stripped away."
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
      (pf--buffer-substring-delimited-whole-buffer pre "^-\}"
           (lambda (sp ep)
             (save-excursion
             (goto-char (- sp 2))
             (push-mark ep)
             (setq mark-active t)
             (delete-region (- sp 2) ep)))))
     (write-file bare-agda))
     (message "%s_Bare.agda has been written." src)))

(define-key pf--menu-bar [pf-show-variationals]
  '(menu-item "Show all registered variationals" pf-show-variationals))

(defun pf-show-variationals ()
  "Show all user declared 𝒱ariationals in another buffer."
 (interactive)
 (occur "𝒱[ \\|-]"))

(define-key pf--menu-bar [pf-show-pfs]
  '(menu-item "Show all concrete PackageFormers" pf-show-pfs))

(defun pf-show-pfs ()
  "Show all user declared PackageFormer's in another buffer."
 (interactive)
 (occur "PackageFormer .* where"))

(define-key pf--menu-bar [pf-fold-annotations]
  '(menu-item "Toggle folding away “700” and “lisp” blocks" pf-fold-annotations))

(defun pf-fold-annotations ()
  "Fold all items enclosed in Agda comments “{- ⋯ -}”."
 (interactive)
 (setq pf-folding (not pf-folding))
 (if pf-folding
     (message "C-c C-l will now fold away “700” and “lisp” blocks. Press ENTER to unfold a block. ")
     (origami-open-all-nodes (current-buffer))
     (message "Blocks “700” and “lisp” have been unfolded.")))

;; Basic origami support for Agda.
(push (cons 'agda2-mode (origami-markers-parser "{-" "-}"))
      origami-parser-alist)

;; Along with a hydra for super quick navigation and easily folding, unfolding blocks!
(defhydra folding-with-origami-mode (global-map "C-c f")
  ("h" origami-close-node-recursively "Hide")
  ("o" origami-open-node-recursively  "Open")
  ("t" origami-toggle-all-nodes  "Toggle buffer")
  ("n" origami-next-fold "Next")
  ("p" origami-previous-fold "Previous"))

;;;###autoload
(define-minor-mode package-former-mode
    "This is an editor extension prototyping “the next 700 module systems” proposed research.

    An informal documentation, with examples, page can be found at
    https://alhassy.github.io/next-700-module-systems-proposal/PackageFormer.html

    The technical matter can be found at https://alhassy.github.io/next-700-module-systems-proposal/

    If you experience anything “going wrong” or have any ideas for improvement,
    please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥
  "
  :lighter " PackageFormer (•̀ᴗ•́)و" ;; Icon to display indicating the mode is enabled.
  :require 'foo

  ;; Toggle the menu bar
  ;; (define-key global-map [menu-bar 700menu] t)(not 700-mode))
  (define-key global-map [menu-bar pf--menu] (and package-former-mode (cons "PackageFormer" pf--menu-bar)))

  (letf (( (symbol-function 'message-box) #'message))
  (if package-former-mode
      ;; Initilisation
      (pf-enable-package-formers)

      ;; Closing
      (pf-disable-package-formers))))

(let ((it (quote ";; p ≈ symptom; f ≈ medicine; adj ≈ neighbouring dependency
;;
(defun graph-map (p f adj xs)
  \"Map the nodes ‘xs’ satisfying ‘p’ by ‘f’.

  ‘f’ is performed on nodes satisfying ‘p’,
  all neighbours are then considered to satisfy p
  and the process repeats recursively.

  E.g., nodes exhibiting symptoms ‘p’ are given medicine ‘f’,
  and their sickness spreads to their neighbours who in turn
  become ill thereby requiring medication, and the process continues.

  ‘adj’ is a binary relation denoting adjacency.
  (adj x y)  ≈  x depends on, or is a neighbour, of y.
  \"

  (let* (;; Using -map instead of -filter since nodes may become sickly later on, position matters.
         (sickly (-map p xs))
         ;; Obtain the items that are currently ‘sickly’.
         (get-sickly (lambda () (--filter it (--zip-with (when it other) sickly xs))))
         ;; infected x  ≡ x has a sickly neighbour
         (infected (λ x → (--any (funcall adj x it) (funcall get-sickly)))))

     ;; Propogate sickness.
     (loop for _ in xs
           do (loop for x in xs
                    for i from 0
                    do (when (funcall infected x) (setf (nth i sickly) t))))

     ;; Apply medication to sickly elements only.
     (--map (if (-contains-p (funcall get-sickly) it) (funcall f it) it) xs)))

;; Example: A graph of 10 nodes, with an edge between multiples; where nodes 3,4,5 are initally ill.
;; (graph-map (λ x → (-contains-p '(3 4 5) x)) (λ x → (format \"medicated-%s\" x)) (λ x y → (zerop (mod x y))) '(1 2 3 4 5 6 7 8 9 10))
;; ⇒ (1 2 medicated-3 medicated-4 medicated-5 medicated-6 7 medicated-8 medicated-9 medicated-10)

(defmacro --graph-map (mark alter elements)
  \"Mark elements in a given list, and recursively mark all those that depend on them.
   Return the list of elements with the marked ones being altered.

   ‘mark’ and ‘alter’ are expressions mentioning ‘it’,
    and so are implicit functional expressions.
  \"
  `(graph-map (λ it → ,mark)
              (λ it → ,alter)
              ;; x depends on y  ≡  x mentions y, with all or no undescores, in its type or equations.
              (λ x y → (or (s-contains? (s-replace \"_\" \" \" (element-name y)) (s-join \" \" (cons (element-type x) (element-equations x))))
                           (s-contains? (element-name y) (s-join \" \" (cons (element-type x) (element-equations x))))))
              ,elements
              ))

(𝒱 record (discard-equations nil) (and-names nil)
 = \"Reify a variational as an Agda “record”.

    By default, elements with equations are construed as
    derivatives of fields  ---the elements
    without any equations.

    ⇨ DISCARD-EQUATIONS is nil by default.
      If provided with a non-nil value, equations are dropped.

    ⇨ AND-NAMES is nil by default and only takes
      effect when DISCARD-EQUATIONS is active.
      If provided with a non-nil value, names with
      equations are dropped altogether.
   \"
  :kind record
  :alter-elements
    (λ es →
      (thread-last es
      ;; Keep or drop eqns depending on “discard-equationals”
      (--graph-map (and discard-equations (element-equations it))
                   (map-equations (-const nil)
                     (map-name (λ n → (if and-names \"_\" n)) it)))
      ;; Discard all “_” named items.
      (--reject (equal \"_\" (element-name it)))
      ;; Unless there's equations, mark elements as fields.
      (--map (map-qualifier
        (λ _ → (unless (element-equations it)
               \"field\")) it)))))

(𝒱 map elements (support-mixfix-names t)
   = \"Apply function ELEMENTS that acts on PackageFormer elements,
      then propogate all new name changes to subsequent elements.

      There is minimal support for mixfix names, but it may be
      ignored by setting SUPPORT-MIXFIX-NAMES to be nil.
     \"
     :alter-elements (lambda (es)
    (let* ((esnew   (mapcar elements es))
           (_       (if support-mixfix-names \"\" \"_\"))
           (names   (--map (s-replace \"_\" _ (element-name it)) es))
           (names′  (--map (s-replace \"_\" _ (element-name it)) esnew)))
      (loop for old in names
            for new in names′
            do (setq esnew (--map (element-replace old new it) esnew)))
      ;; return value
      esnew)))

(𝒱 rename f (support-mixfix-names t)
  =  \"Rename elements using a string-to-string function F acting on names.

      There is minimal support for mixfix names, but it may be
      ignored by setting SUPPORT-MIXFIX-NAMES to be nil.
     \"
     map (λ e → (map-name (λ n → (rename-mixfix f n)) e))
         :support-mixfix-names 'support-mixfix-names)

(𝒱 decorated by
  = \"Rename all elements by suffixing string BY to them.\"
     rename (λ name → (concat name by)))

(𝒱 co-decorated by
  = \"Rename all elements by prefixing string BY to them.\"
     rename (λ name → (concat by name)))

(𝒱 primed
  = \"All elements are renamed with a postfix prime.\"
    decorated \"′\")

(defun reify-to-list (str &optional otherwise)
 \"Given a string of “;”-separated items consisting of “to”-separated pairs,
  interpret it as a Lisp function where “to”-pairs denote mapping clauses.

 E.g., “x₀ to y₀; …; xₙ to yₙ”
 becomes the function sending value xᵢ to yᵢ, and behaves as the identity function
 otherwise unless “otherwise” is provided, in which case it acts as a fallback.

 Concretely:
    (reify-to-list \\\"1 to x; 2 to y; p to q\\\")
  ≈ (λ arg → (pcase arg (\\\"1\\\" \\\"x\\\") (\\\"2\\\" \\\"y\\\") (\\\"p\\\" \\\"q\\\") (otherwise otherwise)))
 \"
 (let (clauses (fallback (or otherwise 'otherwise)))
   (thread-last str
     (s-split \";\")
     (--map (s-split \" to \" it))
     (--map (list (s-trim (car it)) (s-trim (cadr it))))
     (-cons* 'pcase 'arg)
     (setq clauses))
   `(lambda (arg) ,(append clauses `((otherwise ,fallback))))))

(𝒱 renaming by
  = \"Rename elements using BY, a “;”-separated string of “to”-separated pairs.\"
    rename '(reify-to-list by))

(defun to-subscript (n)
  \"Associate a digit ‘n’ with its subscript.\"
  (nth n '(\"₀\" \"₁\" \"₂\" \"₃\" \"₄\" \"₅\" \"₆\" \"₇\" \"₈\" \"₉\")))

(loop for i from 0 to 9
      do (let* ((ᵢ    (to-subscript i))
               (docs (format \"Subscript all elementes by suffixing them with %s.\" i)))
               (eval `(𝒱 ,(intern (format \"subscripted%s\" ᵢ)) = ,docs decorated ,ᵢ))))

(defun is-sort (element)
  \"Check whether the target of ‘element’s type is “Set”. \"
  (s-contains? \"Set\" (target (element-type element))))
  ;; Method ‘target’ is defined in the next subsection, on ADTs.

(𝒱 single-sorted with-sort
  = \"Replace all nullary sorts with the provided WITH-SORT string
     as the name of the new single sort, the universe of discourse.\"
    map (λ e → (if (is-sort e) (map-name (λ _ → with-sort) e) e)))

(defun target (thing)
  \" Given a type-name ‘[name :] τ₀ → ⋯ → τₙ’, yield ‘τₙ’;
    the ‘name’ porition is irrelevant.
  \"
  (car (-take-last 1 (s-split \"→\" thing))))

(𝒱 data carrier
  = \"Reify as an Agda “data” type.

     Only elements targeting CARRIER are kept.
    \"
    :kind  data
    :level dec
    :alter-elements (lambda (es)
      (thread-last es
        (--filter (s-contains? carrier (target (element-type it))))
        (--map (map-type (λ τ → (s-replace carrier $𝑛𝑎𝑚𝑒 τ)) it)))))

(𝒱 generated by
  = \"Keep the largest well-formed PackageFormer whose elements satisfy BY.

     BY is a predicate on elements.
    \"
    :alter-elements  (lambda (fs)
      (let* ( (yeses (--map (funcall by it) fs))
              (get-yeses (lambda () (--filter it (--zip-with (if it other) yeses fs))))
              (in-yeses (lambda (e)
                          (--any
                           (s-contains? (s-replace \"_\" \" \" (element-name e)) (element-type it))
                           (funcall get-yeses)))))

        (loop for _ in fs do
              (loop for f in fs
                    for i from 0
                    do ;; when f in yess, set f to be yes.
                    (when (funcall in-yeses f) (setf (nth i yeses) t))))

        (funcall get-yeses))))

(𝒱 sorts
 = \"Obtaining the types declared in a grouping mechanism.

   For now, only base types; i.e., items targeting “Set”.
   \"
   generated (λ e → (s-contains? \"Set\" (target (element-type e)))))

(defun targets-a-sort (element)
  \"Checks whether the given ‘element’ targets
   any of the sorts of the *current* PacakgeFormer.
   \"
  (--any (s-contains? it (target (element-type element)))
         (-map #'element-name (-filter #'is-sort $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠))))

(𝒱 signature
  = \"Keep only the elements that target a sort, drop all else.\"
    generated (λ e → (targets-a-sort e)))

(𝒱 open with (avoid-mixfix-renaming nil)
  =
    \"Reify a given PackageFormer as a *parameterised* Agda “module” declaration.

     WITH is a renaming, string to string, function that is applied to the parent record that will
     be opened and reexported as a module.

     AVOID-MIXFIX-RENAMING is optional; by default renaming “jumps over” underscores,
     but providing a non-nil value for this argument leaves underscores alone.
     It is a matter of having, say, default “_⊕ₙ_” versus “_⊕_ₙ”.

     The resulting module has a parameter, whose name is irrelevant but is
     of the form “Arg𝒹𝒹𝒹𝒹” for some digits 𝒹 in order to minimise clash with
     any user-defined names.

     Besides the addition of a new parameter, all element qualifiers are discarded.
    \"
    :kind module
    :level none
    :waist 1
    :alter-elements  (lambda (fs)
      (let ((kind \"{! !}\") (ℛ (format \"Ar%s\" (gensym))))
        (cons (make-element :name ℛ :type $𝑝𝑎𝑟𝑒𝑛𝑡)
          (--map (let ((name (if avoid-mixfix-renaming (with (element-name it)) (rename-mixfix with (element-name it)))))
            (make-element :name name
                          :type (format \"let open %s %s in %s\" $𝑝𝑎𝑟𝑒𝑛𝑡 ℛ (element-type it))
                          :equations (list (format \"%s = %s.%s %s\" name $𝑝𝑎𝑟𝑒𝑛𝑡 (element-name it) ℛ)))) fs)))))

(𝒱 opening with
  = \"Open a record as a module exposing only the names mentioned in WITH.

    WITH is a string of “;”-separated items consisting of “to”-separated pairs.
    \"
    open (λ x → (funcall (reify-to-list with \"_\") x)) :avoid-mixfix-renaming t)

    ;; Alternatively, we could have used ‘trash’ names,
    ;; something like (format \"%s\" (gensym)), instead of \"_\".

(𝒱 open-with-decoration ddd
  = \"Open a record, exposing all elements, with decoration DDD.

    DDD is a string.
   \"
   open (λ x → (concat x ddd)))

(defun to-subscript (n)
  \"If i ∈ 0..9, then yield ᵢ, else i.\"
  (if (not (< -1 i 10))
      (format \"%s\" i)
    (nth n '(\"₀\" \"₁\" \"₂\" \"₃\" \"₄\" \"₅\" \"₆\" \"₇\" \"₈\" \"₉\"))))

(defun homify (element sort)
  \"Given a typed name, produce the associating “preservation” formula.
   E.g.,
          _·_    : Scalar → Vector → Vector
          pres-· : {x₁ : Scalar} → {x₂ : Vector} → map₂ (x₁ · x₂) = map₁ x₁ ·′ map₂ x₂

  Type τ gets variable xᵢ provided (i, τ) ∈ sorts; likewise we think of mapᵢ : τ → τ′.
  Notice that the target name is primed, “·′”.
  \"
  (letf* ((sorts     (mapcar #'car sort))
          ((symbol-function 'index) (lambda (s) (to-subscript (cdr (assoc it sort)))))

          (tn→       (s-split \" → \" (element-type element)))
          (arg-count (1- (length tn→)))

          (all-indicies  (--map (index it) (--filter (member (s-trim it) sorts) tn→)))
          (indicies  (-drop-last 1 all-indicies))
          (tgt-idx   (car (-take-last 1 all-indicies)))

          (op        (element-name element))
          (args      (--map (concat \"x\" it) indicies))
          (lhs       (format \"map%s (%s %s)\" tgt-idx op (s-join \" \" args)))

          (op′       (rename-mixfix (lambda (n) (concat n \"′\")) op))
          (map-args  (--map (format \"(map%s x%s)\" it it) indicies))
          (rhs       (format \"%s %s\" op′ (s-join \" \" map-args)))

          (target    (format \"  %s   ≡   %s\" lhs rhs)))

    ;; Change the target type.
    (setq tn→ (--map (when (assoc it sort) (format \"{x%s : %s}\" (index it) it)) tn→))
    (setf (nth arg-count tn→) target)

    ;; Stick it all together, with an updated name.
    (make-element
     :name (format \"pres-%s\" (s-replace \"_\" \"\" (element-name element)))
     :type (s-join \" → \" tn→))))

(𝒱 hom
  = \"Formulate the notion of homomorphism of $𝑝𝑎𝑟𝑒𝑛𝑡 algebras.

     ➩ $𝑝𝑎𝑟𝑒𝑛𝑡 must be an existing record type used in the resulting formulation.
    \"
    record ⟴
    :waist 2
    :alter-elements (lambda (es)

      (let (maps eqns sorts (𝒮𝓇𝒸 \"Src\") (𝒯ℊ𝓉 \"Tgt\"))

        ;; Construct the mapᵢ : sortᵢ → sortᵢ′; keeping track of (sort . i) pairs.
        (loop for e in es
              for i from 1
         do
           (when (is-sort e)
             (push (cons (element-name e) i) sorts)
             (push (make-element
                      :qualifier \"field\"
                      :name (format \"map%s\" (to-subscript i))
                      :type (format \"%s → %s′\" (element-name e) (element-name e)))
                   maps))

            (when (and (targets-a-sort e) (not (is-sort e)))
              (push (homify e sorts) eqns)))

      ;; Ensure we have a source and target space as elements.
      (-cons*
       (make-element :qualifier \"field\" :name 𝒮𝓇𝒸 :type $𝑝𝑎𝑟𝑒𝑛𝑡)
       (make-element :qualifier \"field\" :name 𝒯ℊ𝓉 :type $𝑝𝑎𝑟𝑒𝑛𝑡)
       (--map
        (map-type (λ τ → (format \"let open %s %s; open %s′ %s in %s\"
                                 $𝑝𝑎𝑟𝑒𝑛𝑡 𝒮𝓇𝒸 $𝑝𝑎𝑟𝑒𝑛𝑡 𝒯ℊ𝓉 τ))
                  (map-qualifier (λ _ → \"field\") it))
        (reverse (-concat eqns maps)))))))

(𝒱 unbundling n
 = \"Make the first N elements as parameters to the PackageFormer.

    Any elements in above the waist line have their equations dropped.
    As such, unbundling is not invertible.
   \"
   :waist n
   :alter-elements (λ es →
     (-let [i 0]
       (--graph-map (progn (incf i) (<= i n))
                    (map-equations (-const nil) it)
                    es))))
")))
(setq ♯standard-variationals (s-count-matches-all "(𝒱" it))
(eval (car (read-from-string (format "(progn %s)" it))))
)

(provide 'package-former)
;;; package-former.el ends here
