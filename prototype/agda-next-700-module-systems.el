;;; agda-next-700-module-systems.el --- Making Modules with Meta-Programmed Meta-Primitives, for Agda

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

;; We cannot use lexical binding since the package provides a macro called 𝒱
;; that acts as an interface for a DSL that generates Lisp functions
;; which requires EVAL to bind staged formal arguments to their runtime values.

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
(require 'cl-lib)          ;; New Common Lisp library; ‘cl-???’ forms.

;; (pf--declare-type pf--get-indentation : string integer)
(defun pf--get-indentation (string)
  "How many spaces are there at the front of STRING?

Property: The resulting number is ≤ length STRING."
  (if string (length (s-shared-start string (s-repeat (length string) " "))) 0))

(cl-defun pf--get-children (parent the-wild &key (then #'identity))
  "Returns indented text under a PARENT line.
nil"
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

    ;; How far is the first child indented? At least 1 space; otherwise no children.
    (setq indentation (max 1 (pf--get-indentation (car lines))))

    ;; Keep only the children that have at least this level of indentation.
    (setq lines&more
          (--split-with (<= indentation (pf--get-indentation it)) lines))
    (setq lines (car lines&more))
    (setq unconsidered (cadr lines&more))

    ;; Alter the children according to the given function.
    (setq lines (mapcar then lines))

    ;; Yield the parent line along with the children lines;
    ;; and the unconsumed wild's prefix and suffix.
    `(,prefix ,(cons parent-line lines) ,unconsidered)))

(cl-defun pf--substring-delimited (prefix suffix string)
  "Assuming “STRING ≈ ⋯PREFIX⟪needle⟫SUFFIX⋯”, return the first such needle.
nil"

  (unless (stringp string)
    (error "PF--SUBSTRING-DELIMITED: Argument STRING must be a string"))
  (let* ((new (s-collapse-whitespace string)))
    (when (not (s-blank? prefix))
      (setq new (car (-take-last
                      (if (equal prefix suffix) 2 1) (s-split prefix new)))))
    (when (not (s-blank? suffix))
      (setq new (car (s-split suffix new))))
    (s-trim new)))

(cl-defun pf--substring-delimited-here (context string) "\
Assuming “CONTEXT ≈ PREFIX $here SUFFIX” yield the value of needle ‘$here’.
nil"

  (-let [pre-post (s-split "$here" context)]
    (pf--substring-delimited (s-trim (car pre-post))
                             (s-trim (cadr pre-post))
                             string)))

(defvar pf-folding nil
  "Should 700 and Lisp blocks be folded away when 𝑪-𝑐 𝑪-𝑙.")

;; pf--declare-type has no support for optionals yet
(cl-defun pf--buffer-substring-delimited
    (start end &optional more &key (regexp t))
  "Return next delimited substring in the current buffer.
nil"
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

;; pf--declare-type has no support for optionals yet
(cl-defun pf--buffer-substring-delimited-whole-buffer (start end &optional more)
  "Return all delimited substrings in the current buffer.
nil"
  ;; Colour 700 keywords red “'error”
  (highlight-phrase start 'error)
  (highlight-phrase end 'error)
  (save-excursion
    (let ((l nil) (continue t))
     (goto-char (point-min))

     (while continue
       (condition-case nil
     ;; attemptClause
     (setq l (cons (pf--buffer-substring-delimited start end more) l))
     ;; recoveryBody
     (error (setq continue nil))))

     ;; We've collected items as we saw them, so ‘l’ is in reverse.
    (reverse l))))

(defun rename-mixfix (f op &optional avoid-mixfix-renaming)
  "Rename an operation by “leaping over” Agda positional markers.
nil"
  (let* ((parts (s-split "_" op))
         (front (s-blank? (first parts)))
         (rear (s-blank? (car (last parts)))))

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

(cl-defun pf--extract-imports ()
  "Return substring of buffer whose lines mention “import”.

Throw away any that mention the substring “⟪FileName⟫-generated”."
  (thread-last (buffer-substring-no-properties (point-min) (point-max))
    (s-split "\n")
    (--filter (s-contains? "import " it))
    (--remove (s-contains? (pf--generated-file-name) it))
    (s-join "\n")))

(defmacro λ (&rest body)
  "Implementing Agda style, interactive, lambdas; ideally for inline use:

“λ α β … ω → BODY”  becomes an interactive function with arguments α, …, ω.

The args list may be empty, in which case the separator “→” may be omitted
entirely, if desired.

A BODY must always be supplied, even if the literal nil."
  (let* ((parts (-split-on '→ body)) args rest)

    (if (<= 2 (length parts))
        (progn (setq args (car parts)) (setq rest (cadr parts)))
         ;; Otherwise, only one part was found ---no arguments were provided.
         (setq args nil) (setq rest (car parts)))

   `(lambda ,args (interactive) ,@rest)))

(defstruct pf--package-former
  "Record of components that form a PackageFormer.
nil"
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

(defun $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠-𝑜𝑓 (pf)
 "Return elements of a given PackageFormer's name, PF.

 This is provided to users; it is one of the few utilities that
 makes use of implementation specfic details.
"
 (pf--package-former-elements (cdr (assoc pf pf--package-formers))))

(defvar pf-highlighting t
  "Should PackageFormer syntactical items be coloured?

➩ Yellow for PackageFormer content.
➩ Red for delimiters 700 and Lisp.
➩ Green for names of variationals.")

;; An anaphoric macro ^_^
(defmacro pf--open-pf (p &rest body)
  "Open a package-former P so no qualifiers are required in form BODY."
  `(let*
    ((docstring             (pf--package-former-docstring ,p))
     (kind                  (pf--package-former-kind ,p))
     (name                  (pf--package-former-name ,p))
     (level                 (pf--package-former-level ,p))
     (waist                 (pf--package-former-waist ,p))
     (indentation           (pf--package-former-indentation ,p))
     (elements              (pf--package-former-elements ,p))
     (parameters            (-take waist elements))
     (fields                (-drop waist elements)))
    ,@body))

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
           ,(format "Alter the ‘%s’ field of an ‘element’ value." place)
           (-let [e′ (copy-element e)]
             (setf (,loc e′) (funcall f (,loc e′)))
             e′)))))

(defun element-contains (needle e)
  "Check whether string NEEDLE occurs anywhere in element E."
    (--any it
           (-concat (loop for place in '(element-qualifier element-name element-type)
                         collect (eval `(when (,place e) (s-contains-p needle (,place e)))))
                   (loop for eq in (element-equations e)
                         collect (s-contains-p needle eq)))))

(cl-defun element-replace (old new e &key (support-mixfix-names t))
  "Replace every occurance of word OLD by string NEW in element E.

When SUPPORT-MIXFIX-NAMES is true, we ignore underscores."
  (let* ((e′    (copy-element e))
         (score (if support-mixfix-names "" "_"))
         (old′  (s-replace "_" score old))
         (new′  (s-replace "_" score new)))

    (loop for place in '(element-qualifier element-name element-type)
          do (eval `(when (,place e′) (setf (,place e′)
                          (replace-regexp-in-string (format "\\b%s\\b" old′)
                                                    new′ (,place e′) t t)))))
    ;; Replacements in the equations as well.
    (setf (element-equations e′)
          (loop for eq in (element-equations e′)
                collect (s-replace old′ new′ eq)))
    ;; return value
    e′))

(defun parse-name (element)
  "Given an string representation of an ELEMENT, yield the ‘name’ component.

The shape of the input may be “qualifier lhs ~ rhs” where ‘~’ is either ‘:’
or ‘=’.  The qualifier is a ‘special’ word: field, private."
  (let ((lhs (s-split " " (car (s-split " = " (car (s-split " : " element)))))))
    (if (and (< 1 (length lhs)) (pf--special (nth 0 lhs)))
        (cadr lhs)
      (car lhs))))

(defun parse-elements (elements)
  "Parse string representation of elements into the ‘element’ record type.
nil"
  (-let [es (mapcar #'list elements)]
    ;; Maintain a list of related items.
    (loop for i from 0
          for e in es
          for name = (parse-name (car e))
          do (loop for j from 0 to (1- i)
                   do
                   ;; If the name of ‘e’ occurs in the prefix,
                   ;; then move ‘e’ to the location in the prefix,
                   ;; and zero-out the current location.
                   (when (equal name (parse-name (or (car (nth j es)) "")))
                     ;; Use an empty string in-case the location is nil.
                     (setf (nth j es) (append (nth j es) e))
                     (setf (nth i es) nil))))

    ;; Drop the nils.
    (setq es (--reject (not it) es))

    ;; We now have a list of related items,
    ;; with the car of each being a qualified typed-name
    ;; and the cdr of each being a list of equational clauses
    ;; associated with that name.
    (loop for e in es
          for τ    = (s-split " : " (car e))
          for nom  = (parse-name (car τ))
          for qual = (car (s-split nom (car τ)))
          for _    = (pf--ensure (cdr τ)
                                 (format "Type not supplied for %s!" nom)
                                 (s-join "\n\t\t" (-take 5 elements))
                                 "⋯ Add a type!")
          for ty   = (s-join " : " (cdr τ))
          collect
          (make-element :qualifier (unless (s-blank? qual) qual)
                        :name nom
                        :type ty
                        :equations (cdr e)))))

;; eval-and-compile
(defmacro  -ensure (condition message context &rest suggestions)
  "Ensure provided CONDITION is true, otherwise report an error.
nil"
  `(let* ((ლ\(ಠ益ಠ\)ლ
           (format "700: %s\n\n\t⇨\t%s%s%s" ,message ,context
                   (if (quote ,suggestions) "\n" "")
                   (s-join "\n" (--map (format "\t⇨\t%s" it)
                                       (quote ,suggestions)))))
          ;; Try to evaluate the condition.
          (res (condition-case nil ,condition (error ლ\(ಠ益ಠ\)ლ))))

     ;; If we've made it here, then the condition is defined.
     ;; It remains to check that it's true.
     (or res (error ლ\(ಠ益ಠ\)ლ))))

;; eval-and-compile
(defun -wf (key value &optional context args)
  "Report an error unless provided key-value are well-formed.
nil"
  (let* ((case
            (pcase key
              (:kind `(,(-contains? '(record data module PackageFormer) value)
                       This kind “ ,value ” is not support by Agda!
                       Valid kinds: record⨾ data⨾ module⨾ PackageFormer!))
              (:waist `(,(numberp value)
                        The waist should be a number⨾ which “ ,value ” is not!))
              (:level `(,(-contains? '(inc dec none) value)
                        The “level” must be “inc” or “dec” or “none”⨾
                        which “ ,value ” is not!))))
        (condition (car case))
        (message   (mapconcat #'prin1-to-string (cdr case) " ")))

    ;; TODO: Acount for alter-elements well-formedness?
    ;; (:alter-elements (functionp value)
    ;; (format "Componenet alter-elements should be a function;
    ;; which “%s” is not." value))

    (when case
      ( -ensure (or condition (-contains? args value)) message context))

    ;; Return the key-value as a pair for further processing.
    ;; :kind and :level values are symbols and so cannot be evaluated furthur.
    (cons key
          (if (or (-contains? args value) (-contains? '(:kind :level) key))
              value
            (eval value)))))

(defun pf--load-package-former (lines)
  "Load a string representation of a ‘package-former’ into our global list.
nil"
  (when (not lines)
      (error "PF--LOAD-PACKAGE-FORMER: Error: Input must be non-empty list"))

  (let* (pf
         (header (or (car lines) ""))
         (name (pf--substring-delimited-here "PackageFormer $here :" header))
         (level (pf--substring-delimited-here "Set $here where" header)))

    (when pf-highlighting
      (mapc (λ it → (highlight-phrase (s-trim it) 'hi-yellow)) (cdr lines)))

    (setq pf
          (make-pf--package-former
           :kind                     "PackageFormer"
           :name                     name
           ;; ‘level’ may be “”, that's okay.
           ;; It may be a subscript or implicitly zero, so no space after ‘Set’.
           :level                    level
           :waist                    0
           ;; TODO: Currently no parameter support for arbitrary PackageFormers.
           :indentation              (pf--get-indentation (cadr lines))
           :elements  (parse-elements (--remove (s-starts-with? "-- " it)
                                                (--map (s-trim it)
                                                       (cdr lines))))))

      (push (cons name pf) pf--package-formers)

      ;; return value
      pf))

(defun pf--special (f)
  "Test whether an element F is special or not.
nil"
  (--any? (s-contains? it f) '("field" "private" "open" "top-level" "sibling")))

(cl-defun show-element (e &optional omit-qualifier)
  "Render an ‘element’ value E in the form:

   qualifier name : type ; equational-clause₀ ; ⋯ ; equational-clauseₙ

Optional OMIT-QUALIFIER is useful for when
elements are in a parameter position."
  (s-join " ;\t"
          (cons
           (format "%s%s\t\t: %s"
                   (-let [it (element-qualifier e)]
                     (if (or (not it) omit-qualifier) "" (format "%s " it)))
                   (element-name e)
                   (element-type e))
           (element-equations e))))

(cl-defun pf--show-package-former (pf)
  "Pretty print a package-former PF record value."
  (pf--open-pf pf
    (s-join "\n"
      (-cons*

       ;; The documentation string
       (when docstring (format "{- %s -}" docstring))

       ;; The schema declaration
       (s-collapse-whitespace
        (s-join " "
                (list kind
                      name
                      (s-join " "
                              (--map (concat "("
                                             (show-element it :omit-qualifier)
                                             ")")
                                     parameters))
                      (unless (equal level 'none) (concat ": Set" level))
                      "where")))

       ;; The elements of a PackageFormer
       (thread-last fields
         (--map (format "%s%s"
                        (s-repeat indentation " ")
                        (show-element it))))))))

(eval-and-compile
  (defvar pf--variationals nil
    "Association list of Agda-user defined variational operators."))

(defvar pf-variational-composition-operator "⟴"
  "The operator that composes varitionals.")

(eval-and-compile
(defmacro pf--ensure (condition message context &rest suggestions)
  "Ensure provided CONDITION is true, otherwise report an error.
nil"
  `(let* ((ლ\(ಠ益ಠ\)ლ
           (format "700: %s\n\n\t⇨\t%s%s%s" ,message ,context
                   (if (quote ,suggestions) "\n" "")
                   (s-join "\n" (--map (format "\t⇨\t%s" it)
                                       (quote ,suggestions)))))
          ;; Try to evaluate the condition.
          (res (condition-case nil ,condition (error ლ\(ಠ益ಠ\)ლ))))

     ;; If we've made it here, then the condition is defined.
     ;; It remains to check that it's true.
     (or res (error ლ\(ಠ益ಠ\)ლ)))))

(eval-and-compile
(cl-defun pf--wf (key value &optional context args)
  "Report an error unless provided key-value are well-formed.
nil"
  (let* ((case
            (pcase key
              (:kind `(,(-contains? '(record data module PackageFormer) value)
                       This kind “ ,value ” is not support by Agda!
                       Valid kinds: record⨾ data⨾ module⨾ PackageFormer!))
              (:waist `(,(numberp value)
                        The waist should be a number⨾ which “ ,value ” is not!))
              (:level `(,(-contains? '(inc dec none) value)
                        The “level” must be “inc” or “dec” or “none”⨾
                        which “ ,value ” is not!))))
        (condition (car case))
        (message   (mapconcat #'prin1-to-string (cdr case) " ")))

    ;; TODO: Acount for alter-elements well-formedness?
    ;; (:alter-elements (functionp value)
    ;; (format "Componenet alter-elements should be a function;
    ;; which “%s” is not." value))

    (when case
      (pf--ensure (or condition (-contains? args value)) message context))

    ;; Return the key-value as a pair for further processing.
    ;; :kind and :level values are symbols and so cannot be evaluated furthur.
    (cons key
          (if (or (-contains? args value) (-contains? '(:kind :level) key))
              value
            (eval value))))))

(eval-and-compile
(defun 𝒱𝒸 (body-list &optional context args)
  "Parse a single 𝒱ariational 𝒸lause, “[label] (:key :value)*”, as a list.
nil"
  (let (res)
    (loop for clause in (-split-on '⟴ body-list)
          do (setq res (-concat
                        ;; Symbols starting with “:” are keywords.
                        (if (not (keywordp (car clause)))
                            ;; Function invocation case
                            ;; We turn everything into a string so that we may
                            ;; prepend the function name with a 𝒱-
                            ;; then turn that into Lisp with the first eval
                            ;; then invoke the resulting function call
                            ;; with the second eval.
                            (progn
                              ;; The variational being called is defined.
                              (pf--ensure (fboundp (𝒱- (car clause)))
                                          (format "%s %s “%s” %s"
                                                  "Did you mistype a"
                                                  "variational's name:"
                                                  (car clause)
                                                  "is not defined.")
                                          context
                                          (concat "Use the PackageFormer menu"
                                                  "to see which variationals"
                                                  "are defined."))
                              (eval `( ,(𝒱- (car clause)) ,@(cdr clause))))
                          ;; List of key-value pairs
                          `,(loop for key   in clause by #'cddr
                                  for value in (cdr clause) by #'cddr
                                  collect (pf--wf key value context args)))
                        ;; “pf--wf” is just a fancy “cons”.
                        ;; Newer items c₀ ⟴ ⋯ ⟴ cₙ should be at the
                        ;; front of the list;
                        ;; access should then be using assoc.
                        res)))
    res)))

(eval-and-compile
(defun 𝒱- (name)
  "Prefix the Lisp data NAME with a “𝒱-” then yield that as a Lisp datum."
  (should (symbolp name))
  (thread-last name
    (format "𝒱-%s")
    read-from-string
    car)))

(eval-and-compile
(defmacro 𝒱 (name &rest body)
  "Reify as Lisp a variational declaration using the variational grammar.
nil"
  ;; Main code follows.
  (let* ((context (mapconcat (λ x → (prin1-to-string x t)) (cons name body) " "))
         (args-body (-split-on '= body))
         args pargs kargs argnames docs body res actual-code)
    (pcase (length args-body)
      (2 (setq args (car args-body)
               body (cadr args-body)))
      (_ (setq body (car args-body))))

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
                do (setq give-goal (cl-subst (eval arg) arg give-goal)))

          ;; TODO, maybe.
          ;; "Check that substituted values are well-typed"
          ;; (--map (pf--wf (car it) (or (cdr it)
          ;;                        ;; Mention which argument is not supplied.
          ;;                         (format "No Value for :%s Provided!"
          ;;                       (cdr (assoc (car it) (reverse give-goal₀))))
          )

         give-goal)))

    ;; Now set the code as a documentation string in it, after the fact.
    (setq docs (format "Arguments:\t%s %s\n%s" pargs (reverse kargs)
                       (if (not docs) "Undocumented user-defined variational."
                         ;; Keep paragraph structure, but ignore whitespace.
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
    actual-code)))

(cl-defun pf--load-variational (variation-string)
  "Obtain lines of the buffer that start with “𝒱-” as a Lisp alist.
nil"
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
  "Reify concrete instance declarations as ‘package-former’ values.
nil"
  (letf* (
     (pieces (s-split " " (s-collapse-whitespace line)))
     ($𝑛𝑎𝑚𝑒      (nth 0 pieces))
     ($𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠    nil)
     (eqSymb     (nth 1 pieces))
     ($𝑝𝑎𝑟𝑒𝑛𝑡     (nth 2 pieces))
     (variations (nthcdr 3 pieces))
     (alterations nil)
     (self (copy-pf--package-former (cdr (assoc $𝑝𝑎𝑟𝑒𝑛𝑡 pf--package-formers))))
     (⁉
      ;; If componenet ‘c’ is in the ‘alterations’ list of the
      ;; instance declaration, then evalaute any given ‘more’ code,
      ;; get the value for ‘c’ and turn it
      ;; into a string, if ‘str’ is true, then set the new PackageFormer's ‘c’
      ;; componenet to be this value.
      ;; Well-formedness checks happen at the 𝒱 and 𝒱𝒸 stages, see below.
      (lambda (c &optional str more)
        (when-let ((it (cdr (assoc (intern (format ":%s" c)) alterations))))
          (eval `(progn ,@more))
          (when str (setq it (format "%s" it)))
          (eval `(setf (,(car (read-from-string
                               (format "pf--package-former-%s" c))) self)
                       it))))))

    ;; Ensure instance declaration is well-formed.
    (pf--ensure (and (not (s-blank? (s-trim $𝑛𝑎𝑚𝑒))) (equal "=" eqSymb) $𝑝𝑎𝑟𝑒𝑛𝑡)
                (concat "An instance declaration is of the form "
                        "“new-name = parent-package-former "
                        "variational-clauses”.")
                line)

    ;; Let's not overwrite existing PackageFormers.
    (pf--ensure (not (assoc $𝑛𝑎𝑚𝑒 pf--package-formers))
                (format "PackageFormer “%s” is already defined; use a new name."
                        $𝑛𝑎𝑚𝑒)
                line)

    ;; Ensure the PackageFormer to be instantiated is defined.
    (pf--ensure self
                (format "Parent “%s” not defined." $𝑝𝑎𝑟𝑒𝑛𝑡)
                line
                "Use the PackageFormer Emacs menu to see which PackageFormers are defined."
                "Perhaps you did not enclose the parent in 700-comments?")

    ;; Update the new PackageFormer with a docstring of its instantiation
    ;; as well as its name.
    (setf (pf--package-former-docstring self) line)
    (setf (pf--package-former-name self) $𝑛𝑎𝑚𝑒)
    (setq $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠 ; Copy so that user does not inadvertently
                  ; alter shared memory locations!
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
      (funcall ⁉ 'kind 'string-please)

      ;; :waist ≈ The division between parameters and remaining elements.
      (funcall ⁉ 'waist)

      ;; :level ≈ Either 'inc or 'dec, for increment or decrementing the level.
      (funcall ⁉ 'level nil ;; 'string-please
         '((let* ((lvl (pf--package-former-level self))
                  (toLevel (lambda (n)
                             (s-join "" (-concat (-repeat n "Level.suc (")
                                                 (list "Level.zero")
                                                 (-repeat n ")")))))
                 (subs `("" "₁" "₂" "₃" "₄" "₅" "₆" "₇" "₈" "₉"
                         ,(funcall toLevel 10)))
                 (here (-elem-index (s-trim lvl) subs)))
             (setq it
                   (if here

                       (pcase it
                         ('inc (nth (1+ here) subs))
                         ('dec (nth (1- here) subs)))

                     (pcase it
                       ('inc (format "Level.suc (%s)" lvl))
                       ('dec (s-join "suc"
                                     (cdr (s-split "suc" lvl :omit-nulls)))))))

             (unless it (setq it 'none)))))

      ;; :alter-elements ≈ Access the typed name constituents list.
      ;; Perform *all* element alterations,
      ;; in the left-to-right ⟴ order; if any at all.
      (loop for ae in (reverse (mapcar #'cdr (--filter
                                              (equal ':alter-elements (car it))
                                              alterations)))
            do
            (setq $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠
                  (cl-remove-duplicates (--filter it (funcall ae $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠))
                                     :test #'equal :from-end t)))
              ;; Filter in only the non-nil constituents & those not
              ;; starting with “--” & remove duplicates.
              ;; We do this each time, rather than at the end, since
              ;; variationals may loop over all possible elements and we do not
              ;;  want to consider intermediary nils or duplicates.
      (setf (pf--package-former-elements self) $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠)

      ;; We've just formed a new PackageFormer, which can be modified,
      ;; specialised, later on.
      (add-to-list 'pf--package-formers (cons $𝑛𝑎𝑚𝑒 self))
      (when show-it (pf--show-package-former self))))

(defvar pf--annotations nil
  "The contents of the PackageFormer annotations.

If this variable does not change, we short-circut all processing.")

(cl-defun pf--load-pf--annotations ()
  "Parse and load {-700⋯-} syntax.
nil"
  (interactive)

  ;; First, let's run all the lisp. We enclose each in a progn in-case the user
  ;; has multiple forms in a single lisp-block.
  (loop for (lispstart . lispend) in '(("^\{-lisp" . "^-\}"))
        do (loop for lispstr in
                 (pf--buffer-substring-delimited-whole-buffer lispstart lispend)
                 do
                 (eval (car (read-from-string (format "(progn %s)" lispstr))))))

  ;; For now, ‘item’ is a PackageFormer,
  ;; instantiation declaration, or other Agda code.
  (let (item lines 700-cmnts)

    ;; Catenate all pf--annotations into a single string.
    (setq 700-cmnts (s-join "\n"
                            (pf--buffer-substring-delimited-whole-buffer
                             "^\{-700"
                             "^-\}")))

    (if (equal pf--annotations 700-cmnts)

        (message "pf--annotations Unchanged.")

      ;; Update global.
      (setq pf--annotations 700-cmnts)

      ;; View comments as a sequence of lines, ignore empty lines
      ;; ---which are not in our grammar.
      (setq lines (--remove (s-blank? (s-collapse-whitespace it))
                            (s-lines pf--annotations)))

      ;; Traverse the pf--annotations:
      ;; ➩ Skip comments; lines starting with “-- ”.
      ;; ➩ If we see a “𝒱-lhs = rhs” equation, then load it as a variational.
      ;; ➩ If we view a “lhs = rhs” equation, then load it as an
      ;;   instance delcaration.
      ;; ➩ If we view a PackageFormer declaration, then load it into our
      ;;   package-formers list.
      (while lines
        (setq item (car lines))

        (if (not (s-blank? (s-shared-start "-- " (s-trim item))))
            (setq lines (cdr lines))

          (if (not (s-blank? (s-shared-start "𝒱-" item)))
              (progn (pf--load-variational item) (setq lines (cdr lines)))

            (if (s-contains? " = " item)
                (progn (pf--load-instance-declaration item)
                       (setq lines (cdr lines)))

              ;; Else we have a PackageFormer declaration
              ;; and other possiblly-non-700 items.
              (setq item (pf--get-children "PackageFormer" lines))

              ;; port non-700 items to generated file
              (push (cons 'porting (s-join "\n" (car item)))
                    pf--package-formers)

              ;; acknowledge PackageFormer declaration, if any
              (when (cadr item) (pf--load-package-former (cadr item)))

              ;; Update lines to be the unconsidered porition
              ;; of the wild comments.
              (setq lines (caddr item))))))

      (message "Finished parsing pf--annotations."))))

;; Nearly instantaneous display of tooltips.
(setq tooltip-delay 0)

;; Give user 30 seconds before tooltip automatically disappears.
(setq tooltip-hide-delay 30)

(defun pf--tooltipify (phrase notification)
  "Add a tooltip to every instance of PHRASE to show NOTIFICATION.
nil"
  (should (stringp phrase))
  (should (stringp notification))
  (save-excursion  ;; Return cursour to current-point afterwards.
    (goto-char 1)
    ;; The \b are for empty-string at the start or end of a word.
    (while (search-forward-regexp (format "\\b%s\\b" phrase) (point-max) t)
      (put-text-property (match-beginning 0)
                         (match-end 0)
                         'help-echo
                         (s-trim notification)))))

(defun pf--insert-generated-import (name-of-generated-file)
  "Insert an import pointing to the generated file.

In the current file, find the top-most module declaration
then insert an import to NAME-OF-GENERATED-FILE."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (condition-case _
        ;; attemptClause:
        (re-search-forward (concat "open import " name-of-generated-file))
      ;; recoveryBody:
      (error ;; (message-box (format "%s" the-err))
       (re-search-forward "\\(module.*\\)")
       (replace-match (concat "\\1\nopen import " name-of-generated-file))))))

(defvar pf-waiting-for-agda-threshhold 14 "\
How long we should wait for Agda before giving up on colouring and tooltips.

Default is to wait 4 × 0.5 milliseconds.
Why? An inital ‘agda2-load’ of a ~300 line file may take some time.")

(defun pf--reify-package-formers (orig-fun &rest args)
  "Parse package-former syntax and produce Agda when possible.

ORIG-FUN is intended to be the Agda loading process with arguments ARGS."
  (interactive)
  (let* (printed-pfs
        (parent-dir (s-join "/"
                            (-drop-last 1 (s-split "/" buffer-file-truename))))
        (generatedmodule  (pf--generated-file-name))
        (newfile (concat parent-dir "/" generatedmodule ".agda"))
        (parent-imports (pf--extract-imports)))

    ;; Load variationals, PackageFormers, instantiations, and porting list.
    ;; Setting the following to nil each time is not ideal.
    (setq	pf--variationals
             (-take-last ♯standard-variationals pf--variationals)
             ;; take last n items, those being exported into the .el.
             pf--package-formers       nil
             pf--annotations           nil)

    (pf--load-pf--annotations)

    (with-temp-buffer
      (goto-char (point-min))

      ;; Copy/paste imports from parent file.
      (insert (s-join "\n" `(
         "{- This file is generated ;; do not alter. -}\n"
         ,parent-imports
         "open import Level as Level using (Level)"
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

      (write-region (goto-char (point-min)) (goto-char (point-max)) newfile))

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
      (when (> counter pf-waiting-for-agda-threshhold)
        (error (concat "PackageFormer ∷ "
                       "Items generated, but not coloured; "
                       "Agda seems busy...")))
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

(defvar pf--menu-bar (make-sparse-keymap "PackageFormer"))

(define-key pf--menu-bar [pf-enable-package-formers]
  '(menu-item "Enable PackageFormer Generation" pf-enable-package-formers))

(defun pf-enable-package-formers ()
 "Add a menubar, and make Agda's 𝑪-𝑐 𝑪-𝒍 consider package-former syntax."
 (interactive)
 (define-key global-map [menu-bar pf--menu] (cons "PackageFormer" pf--menu-bar))
 (advice-add 'agda2-load :around #'pf--reify-package-formers)
 (message-box (concat "C-c C-l now reifies PackageFormer annotations"
                      "into legitimate Agda.")))

(define-key pf--menu-bar [pf-disable-package-formers]
  '(menu-item "Disable PackageFormer Generation" pf-disable-package-formers))

(defun pf-disable-package-formers ()
  "Remove menubar, and make Agda's 𝑪-𝑐 𝑪-𝒍 act as normal."
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
 (switch-to-buffer "*PackageFormer-About*") (insert "\
This is an editor extension prototyping “the next 700 module systems”
proposed research.

An informal documentation, with examples, page can be found at
https://alhassy.github.io/next-700-module-systems/prototype/package-former.html

The technical matter can be found at
https://alhassy.github.io/next-700-module-systems/

If you experience anything “going wrong” or have any ideas for improvement,
please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥"))

(define-key pf--menu-bar [pf--bare-bones]
  '(menu-item "Copy file with PackageFormer annotations stripped away"
              pf--bare-bones))

(defun pf-bare-bones ()
  "Duplicate the current buffer with PackageFormer annotations stripped away."
 (interactive)
 (let* ((src (file-name-sans-extension (buffer-name)))
        (src-agda (format "%s.agda" src))
        (bare-agda (format "%s-bare.agda" src)))
   (with-temp-buffer
     (insert-file-contents src-agda)
     (goto-char (point-min))
       (re-search-forward (format "module %s" src))
       (replace-match (format "module %s-bare" src))
     (loop for pre in '("^\{-lisp" "^\{-700")
      do
      (goto-char (point-min))
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
  '(menu-item "Toggle folding away “700” and “lisp” blocks"
              pf-fold-annotations))

(defun pf-fold-annotations ()
  "Fold all items enclosed in Agda comments “{- ⋯ -}”."
  (interactive)
  (setq pf-folding (not pf-folding))
  (if pf-folding
      (message "Use “C-c f t” to toggle folding blocks")
    (origami-open-all-nodes (current-buffer))
    (message "Blocks “700” and “lisp” have been unfolded.")))

;; Basic origami support for Agda.
(push (cons 'agda2-mode (origami-markers-parser "{-" "-}"))
      origami-parser-alist)

;; Along with a hydra for super quick navigation
;; and easily folding, unfolding blocks!
(defhydra folding-with-origami-mode (global-map "C-c f")
  ("h" origami-close-node-recursively "Hide")
  ("o" origami-open-node-recursively  "Open")
  ("t" origami-toggle-all-nodes  "Toggle buffer")
  ("n" origami-next-fold "Next")
  ("p" origami-previous-fold "Previous"))

;;;###autoload
(define-minor-mode agda-next-700-module-systems-mode "\
An editor extension prototyping “the next 700 module systems” proposed research.

An informal documentation, with examples, page can be found at
https://alhassy.github.io/next-700-module-systems-proposal/PackageFormer.html

The technical matter can be found at
https://alhassy.github.io/next-700-module-systems-proposal/

If you experience anything “going wrong” or have any ideas for improvement,
please contact Musa Al-hassy at alhassy@gmail.com; thank-you ♥‿♥"
  ;; Icon to display indicating the mode is enabled.
  :lighter " PackageFormer (•̀ᴗ•́)و"
  :require 'foo

  ;; Toggle the menu bar
  (define-key global-map [menu-bar pf--menu]
    (and agda-next-700-module-systems-mode (cons "PackageFormer" pf--menu-bar)))

  (letf (( (symbol-function 'message-box) #'message))
    (if agda-next-700-module-systems-mode
        ;; Initilisation
        (pf-enable-package-formers)

      ;; Closing
      (pf-disable-package-formers))))

(eval-and-compile ;; begin eval-and-compile for standard library of 𝒱ariationals

  (cl-defun element-retract (parent es &key (new es))
    "Realise a list of elements as an Agda no-op record.
  
  E.g., list “Carrier : Set; e : Carrier”
  maps to the following element value.
  
        toParent : parent
        toParent = record {Carrier = Carrier; e = e}
  
  See also 𝒱-renaming, which may be useful to change ‘toParent’.
  
  NEW is a new updated version of ES, if any.
  "
  
    (-let [toParent (format "to%s" parent)]
      (car (parse-elements (list
        (format "%s : let View X = X in View %s" toParent parent)
        (format "%s = record {%s}" toParent
  
          (s-join ";"
          (loop for e  in es
                for e′ in new
                unless (or (s-contains-p "let View X = X" (element-type e)) ;; Ignore source view morphisms
                           (element-equations e))                           ;; Ignore “derivied” elements
                collect (format "%s = %s" (element-name e) (element-name e′))))))))))
  
  (𝒱 extended-by ds
     = "Extend a given presentation by a list of ;-separated declarations.
  
        The resuling presentation has a “toX” retract method,
        where ‘X’ is the parent presentation.
       "
       :alter-elements (λ es → (-concat es (parse-elements (mapcar #'s-trim (s-split ";" ds))) (list (element-retract $𝑝𝑎𝑟𝑒𝑛𝑡 es)))))
  (𝒱 union pf
   = "Union parent PackageFormer with given PF.
  
  Union the elements of the parent PackageFormer with those of
  the provided PF, then adorn the result with two views:
  One to the parent and one to the provided PF.
  
  If an identifer is shared but has different types, then crash.
  "
   :alter-elements (λ es →
      (-concat
         es
         ($𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠-𝑜𝑓 pf)
         (list (element-retract $𝑝𝑎𝑟𝑒𝑛𝑡 es)
               (element-retract pf ($𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠-𝑜𝑓 pf))))))
  (defun flip-type (τ)
    "Given a binary operation's type, as a string, flip the first two types.
  
  E.g., “A → B → C” becomes “B → A → C”.
    "
    (-let [ts (s-split "→" τ)]
     (s-join " → " (list (nth 1 ts) (nth 0 ts) (nth 2 ts)))))
  (defun flip (name op)
   "If element OP is named NAME, then flip its type; else leave it alone-ish.
  
  If OP mentions NAME, then prefix its type with
  “let NAME = λ x y → NAME y x in”, which results in valid Agda
  due to its identifier scoping rules.
  "
   (cond ((equal name (element-name op))
                 (map-type #'flip-type op))
         ((element-contains (s-replace "_" "" name) op)
                 (-let [letin (format "let %s = λ x y → %s y x in " name name)]
                   (thread-last op
                     (map-type (λ τ → (concat letin τ)))
                     (map-equations (λ eqs → (--map (-let [ps (s-split "=" it)] (format "%s = %s %s" (car ps) letin (s-join "=" (cdr ps)))) eqs))))))
         (t op)))
  (𝒱 flipping name (renaming "")
   = "Flip a single binary operation, or predicate, NAME.
  
      Dual constructs usual require some identifiers to be renamed,
      and these may be supplied as a “;”-separated “to”-separated string list, RENAMING.
  
      There is no support for underscores; mixfix names must be given properly.
    "
      renaming 'renaming :adjoin-retract nil
   ⟴ :alter-elements (λ es →
                        (let ((es′ (--map (flip name it) es)))
                          (-concat es′ (list (flip name (element-retract $𝑝𝑎𝑟𝑒𝑛𝑡 ($𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠-𝑜𝑓 $𝑝𝑎𝑟𝑒𝑛𝑡) :new es′)))))))
  (defvar ♯standard-variationals 10
    "The number of variationals exported with the PackageFormer system.")
  ;; p ≈ symptom; f ≈ medicine; adj ≈ neighbouring dependency
  ;;
  (cl-defun graph-map (p f adj xs &optional keep-only-marked)
    "Map the nodes XS satisfying P by F along adjacency ADJ.
  nil"
    (let* (;; Using -map instead of -filter since nodes may become
           ;; sickly later on, position matters.
           (sickly (-map p xs))
           ;; Obtain the items that are currently ‘sickly’.
           (get-sickly (lambda ()
                         (--filter it (--zip-with (when it other) sickly xs))))
           ;; infected x  ≡ x has a sickly neighbour
           (infected (λ x → (--any (funcall adj x it) (funcall get-sickly)))))
  
       ;; Propogate sickness.
       (loop for _ in xs
             do (loop for x in xs
                      for i from 0
                      do (when (funcall infected x) (setf (nth i sickly) t))))
  
       ;; Apply medication to sickly elements only.
       (--filter it (--map (if (-contains-p (funcall get-sickly) it)
                  (funcall f it)
                  (unless keep-only-marked it))
              xs))))
  (cl-defmacro --graph-map (mark alter elements &optional (keep-only-marked t))
    "Recursively ALTER and MARK elements and their dependents.
  nil"
    `(graph-map (λ it → ,mark)
                (λ it → ,alter)
                ;; x depends on y  ≡  x mentions y, with all or no undescores,
                ;;                    in its type or equations.
                (λ x y →
                   (or (s-contains? (s-replace "_" " " (element-name x))
                                    (s-join " " (cons (element-type y)
                                                      (element-equations y))))
                       (s-contains? (element-name x)
                                    (s-join " " (cons (element-type y)
                                                      (element-equations y))))))
                ,elements ,keep-only-marked))
  (𝒱 record (discard-equations nil) (and-names nil)
   = "Reify a variational as an Agda “record”.
  
      By default, elements with equations are construed as
      derivatives of fields  ---the elements
      without any equations.
  
      ⇨ DISCARD-EQUATIONS is nil by default.
        If provided with a non-nil value, equations are dropped indiscriminately.
  
      ⇨ AND-NAMES is nil by default and only takes
        effect when DISCARD-EQUATIONS is active.
        If provided with a non-nil value, names with
        equations are dropped altogether; but some may be kept
        if they are needed for some fields to be well-defined.
     "
    :kind record
    :alter-elements
      (λ es →
        (thread-last es
  
        (funcall (λ es′ → (if (not discard-equations) es′
                 (--map (map-equations (-const nil) (map-qualifier (-const (when (element-equations it) 'eqns)) it)) es′))))
  
        (funcall (λ es′ → (if (not and-names) es′
          (--graph-map (not (equal 'eqns (element-qualifier it))) it es′))))
  
        ;; Unless there's equations, mark elements as fields.
        (--map (map-qualifier
          (λ _ → (unless (element-equations it)
                 "field")) it)))))
  (𝒱 unbundling n
   = "Make the first N elements as parameters to the PackageFormer.
  
      Any elements in above the waist line have their equations dropped.
      As such, unbundling is not invertible.
     "
     :waist n
     :alter-elements (λ es →
       (-let [i 0]
         (--graph-map (progn (incf i) (<= i n))
                      (map-equations (-const nil) it)
                      es))))
  (𝒱 map elements (support-mixfix-names t) (adjoin-retract nil)
     = "Apply function ELEMENTS that acts on PackageFormer elements,
        then propogate all new name changes to subsequent elements.
  
        There is minimal support for mixfix names, but it may be
        ignored by setting SUPPORT-MIXFIX-NAMES to be nil.
  
        When ADJOIN-RETRACT is non-nil, we adjoin a “record {oldᵢ = nameᵢ}”
        view morphism; i.e., record translation.
  
        Clauses “f = f” are considered to occur only in views, record translations,
        and so only the RHS occurance is updated to a new name.
        C.f. the definition of element-retract.
        "
       :alter-elements (lambda (es)
  
      (let* ((es′    (mapcar elements es))
             (names  (mapcar #'element-name es))
             (names′ (mapcar #'element-name es′)))
  
        ;; Replace all occurances of old names with corresponding new ones.
        (loop for old in names
              for new in names′
              do (setq es′ (--map (element-replace old new it :support-mixfix-names support-mixfix-names) es′)))
  
       ;; Account for “f = f” translations; c.f., element-retract.
       (loop for old in names
             for new in names′
             for offend  = (format "%s = %s" new new)
             for correct = (format "%s = %s" old new)
             do  (setq es′ (loop for e′ in es′
             collect (if (element-contains offend e′)
                         (element-replace offend correct e′ :support-mixfix-names nil)
                         e′))))
       ;; return value
       (-concat es′ (when adjoin-retract (list (element-retract $𝑝𝑎𝑟𝑒𝑛𝑡 es :new es′)))))))
  (𝒱 rename f (support-mixfix-names t) (adjoin-retract t)
    =  "Rename elements using a string-to-string function F acting on names.
  
        There is minimal support for mixfix names, but it may be
        ignored by setting SUPPORT-MIXFIX-NAMES to be nil.
  
        When ADJOIN-RETRACT is non-nil, we adjoin a “record {oldᵢ = nameᵢ}”
        view morphism; i.e., record translation.
       "
       map (λ e → (map-name (λ n → (rename-mixfix f n)) e))
           :support-mixfix-names 'support-mixfix-names
           :adjoin-retract 'adjoin-retract)
  (𝒱 decorated by
    = "Rename all elements by suffixing string BY to them."
       rename (λ name → (concat name by)))
  
  (𝒱 co-decorated by
    = "Rename all elements by prefixing string BY to them."
       rename (λ name → (concat by name)))
  
  (𝒱 primed
    = "All elements are renamed with a postfix prime."
      decorated "′")
  ;; Neato: (reify-to-list "x₀; ⋯; xₙ" nil) ⇒ (λ x ↦ If ∃ i • x ≈ xᵢ then "" else nil)
  ;; KEY is a function applied to the input argument /before/ casing on LHS ↦ RHS names.
     (cl-defun reify-to-list (str &key (otherwise 'otherwise) (key #'identity))
     "Transform “to list” STR with default OTHERWISE into a Lisp function.
  nil"
     (let (clauses)
       (thread-last str
         (s-split ";")
         (--map (s-split " to " it))
         (--map (list (s-trim (car it)) (s-trim (or (cadr it) "")))) ;; accomodate empty str.
         (-cons* 'pcase `(,key arg))
         (setq clauses))
       `(lambda (arg) ,(append clauses `((otherwise ,otherwise))))))
  
  (𝒱 renaming by (adjoin-retract t)
    = "Rename elements using BY, a “;”-separated string of “to”-separated pairs.
  
        When ADJOIN-RETRACT is non-nil, we adjoin a “record {oldᵢ = nameᵢ}”
        view morphism; i.e., record translation.
  "
      rename '(reify-to-list by) :adjoin-retract 'adjoin-retract)
  (defun to-subscript (n)
    "Associate digit N with its subscript.
  
  If N ∈ 0..9, then yield ₙ, else N."
  
    (or (nth n '("₀" "₁" "₂" "₃" "₄" "₅" "₆" "₇" "₈" "₉")) n))
  
  ;; Let's make a family of variationals.
  (loop for i from 0 to 9
        for ᵢ    = (to-subscript i)
        for docs = (format "Subscript all elementes by suffixing them with %s." i)
        do (eval `(𝒱 ,(intern (format "subscripted%s" ᵢ)) = ,docs decorated ,ᵢ)))
  (defun is-sort (element)
    "Check whether the target of ELEMENT’s type is ‘Set’."
    (s-contains? "Set" (target (element-type element))))
    ;; Method ‘target’ is defined in the next subsection, on ADTs.
  
  (𝒱 single-sorted with-sort
    = "Replace all nullary sorts with the provided WITH-SORT string
       as the name of the new single sort, the universe of discourse."
      map (λ e → (if (is-sort e) (map-name (λ _ → with-sort) e) e)))
  (defun target (thing)
    "Return final type mentioned in THING, a string declaration.
  
  Given a type-name ‘[name :] τ₀ → ⋯ → τₙ’, yield ‘τₙ’;
  the ‘name’ porition is irrelevant."
    (car (-take-last 1 (s-split "→" thing))))
  (𝒱 data carrier
    = "Reify as an Agda “data” type.
  
       Only elements targeting CARRIER are kept.
      "
      :kind  data
      :level dec
      :alter-elements (lambda (es)
        (thread-last es
          (--filter (s-contains? carrier (target (element-type it))))
          (--map (map-type (λ τ → (s-replace carrier $𝑛𝑎𝑚𝑒 τ)) it)))))
  (𝒱 generated by
    = "Keep the largest well-formed PackageFormer whose elements satisfy BY.
  
       BY is a predicate on elements.
      "
      :alter-elements (λ es → (--graph-map (funcall by it) it es)))
  
  (𝒱 sorts
   = "Obtaining the types declared in a grouping mechanism.
  
     For now, only base types; i.e., items targeting “Set”.
     "
     generated (λ e → (s-contains? "Set" (target (element-type e)))))
  (defun targets-a-sort (element)
    "Check whether the given ELEMENT targets a sort.
  
  The sorts considered refer to those of the *current* PacakgeFormer."
    (--any (s-contains? it (target (element-type element)))
           (-map #'element-name (-filter #'is-sort $𝑒𝑙𝑒𝑚𝑒𝑛𝑡𝑠))))
  
  (𝒱 signature
    = "Keep only the elements that target a sort, drop all else."
      generated (λ e → (targets-a-sort e)))
  (𝒱 open with (avoid-mixfix-renaming nil)
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
                            :type (format "let open %s %s in %s" $𝑝𝑎𝑟𝑒𝑛𝑡 ℛ (element-type it))
                            :equations (list (format "%s = %s.%s %s" name $𝑝𝑎𝑟𝑒𝑛𝑡 (element-name it) ℛ)))) fs)))))
  (𝒱 opening with
    = "Open a record as a module exposing only the names mentioned in WITH.
  
      WITH is a string of “;”-separated items consisting of “to”-separated pairs.
      "
      open (λ x → (funcall (reify-to-list with "_") x)) :avoid-mixfix-renaming t)
  
      ;; Alternatively, we could have used ‘trash’ names,
      ;; something like (format "%s" (gensym)), instead of "_".
  (𝒱 open-with-decoration ddd
    = "Open a record, exposing all elements, with decoration DDD.
  
      DDD is a string.
     "
     open (λ x → (concat x ddd)))
  (defun homify (element sort)
    "Given a typed name, produce the associating “preservation” formula.
  
  E.g.,
    _·_    : Scalar → Vector → Vector
    pres-· : {x₁ : Scalar} → {x₂ : Vector} → map₂ (x₁ · x₂) = map₁ x₁ ·′ map₂ x₂
  
  
  Type τ gets variable xᵢ provided (i, τ) ∈ SORT;
  likewise we think of mapᵢ : τ → τ′.
  Notice that the target name is primed, “·′”
  
  ELEMENT is the typed-name and SORT is the alist of numbered sorts."
    (letf* ((sorts     (mapcar #'car sort))
            (index     (λ it → (to-subscript (cdr (assoc it sort)))))
  
            (tn→       (s-split " → " (element-type element)))
            (arg-count (1- (length tn→)))
  
            (all-indicies  (mapcar index
                                   (--filter (member (s-trim it) sorts) tn→)))
            (indicies  (-drop-last 1 all-indicies))
            (tgt-idx   (car (-take-last 1 all-indicies)))
  
            (op        (element-name element))
            (args      (--map (concat "x" it) indicies))
            (lhs       (format "map%s (%s %s)" tgt-idx op (s-join " " args)))
  
            (op′       (rename-mixfix (lambda (n) (concat n "′")) op))
            (map-args  (--map (format "(map%s x%s)" it it) indicies))
            (rhs       (format "%s %s" op′ (s-join " " map-args)))
  
            (target    (format "  %s   ≡   %s" lhs rhs)))
  
      ;; Change the target type.
      (setq tn→ (--map (when (assoc it sort)
                         (format "{x%s : %s}" (funcall index it) it)) tn→))
      (setf (nth arg-count tn→) target)
  
      ;; Stick it all together, with an updated name.
      (make-element
       :name (format "pres-%s" (s-replace "_" "" (element-name element)))
       :type (s-join " → " tn→))))
  (𝒱 hom
    = "Formulate the notion of homomorphism of $𝑝𝑎𝑟𝑒𝑛𝑡 algebras.
  
       ➩ $𝑝𝑎𝑟𝑒𝑛𝑡 must be an existing record type used in the resulting formulation.
      "
      record ⟴
      :waist 2
      :alter-elements (lambda (es)
  
        (let (maps eqns sorts (𝒮𝓇𝒸 "Src") (𝒯ℊ𝓉 "Tgt"))
  
          ;; Construct the mapᵢ : sortᵢ → sortᵢ′; keeping track of (sort . i) pairs.
          (loop for e in es
                for i from 1
           do
             (when (is-sort e)
               (push (cons (element-name e) i) sorts)
               (push (make-element
                        :qualifier "field"
                        :name (format "map%s" (to-subscript i))
                        :type (format "%s → %s′" (element-name e) (element-name e)))
                     maps))
  
              (when (and (targets-a-sort e) (not (is-sort e)))
                (push (homify e sorts) eqns)))
  
        ;; Ensure we have a source and target space as elements.
        (-cons*
         (make-element :qualifier "field" :name 𝒮𝓇𝒸 :type $𝑝𝑎𝑟𝑒𝑛𝑡)
         (make-element :qualifier "field" :name 𝒯ℊ𝓉 :type $𝑝𝑎𝑟𝑒𝑛𝑡)
         (--map
          (map-type (λ τ → (format "let open %s %s; open %s′ %s in %s"
                                   $𝑝𝑎𝑟𝑒𝑛𝑡 𝒮𝓇𝒸 $𝑝𝑎𝑟𝑒𝑛𝑡 𝒯ℊ𝓉 τ))
                    (map-qualifier (λ _ → "field") it))
          (reverse (-concat eqns maps)))))))

) ;; End eval-and-compile for standard library of 𝒱ariationals

(provide 'agda-next-700-module-systems)
;;; agda-next-700-module-systems.el ends here
