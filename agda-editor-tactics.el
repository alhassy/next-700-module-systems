;;; agda-editor-tactics.el --- An editor tactic to produce Σ-types from Agda records  -*- lexical-binding: t; -*-

;; Copyright (c) 2021 Musa Al-hassy

;; Author: Musa Al-hassy <alhassy@gmail.com>
;; Version: 1.0
;; Package-Requires: ((s "1.12.0") (dash "2.16.0") (emacs "27.1") (org "9.1"))
;; Keywords: abbrev, convenience, languages, agda, tools
;; URL: https://github.com/alhassy/next-700-module-systems

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; Agda uses a number of editor tactics, such as C-c C-c, to perform case
;; analysis or to extract inner definitions to the toplevel. We add a new
;; tactic.
;;
;; Select an Agda record, then press M-x agda-editor-tactics-as-Σ:nested,
;; tabbing along the way, to obtain a transformed Σ-product form of the record.
;;
;; This tactic was requested in the Agda mailing list,
;; I will likely produce other tactics as requested ---time permitting.
;;
;; This file has been tangled from a literate, org-mode, file.

;;; Code:

;; String and list manipulation libraries
;; https://github.com/magnars/dash.el
;; https://github.com/magnars/s.el

(require 's)               ;; “The long lost Emacs string manipulation library”
(require 'dash)            ;; “A modern list library for Emacs”
(require 'cl-lib)          ;; New Common Lisp library; ‘cl-???’ forms.

(defconst agda-editor-tactics-version (package-get-version))
(defun agda-editor-tactics-version ()
  "Print the current agda-editor-tactics version in the minibuffer."
  (interactive)
  (message agda-editor-tactics-version))

;;;###autoload
(define-minor-mode agda-editor-tactics-mode
    "An Emacs editor tactic to produce Σ-types from Agda records."
  nil nil nil
  (if agda-editor-tactics-mode
      (progn
        ;; Give users interactive access to this function at the top level.
        (agda-editor-tactics-regonify agda-editor-tactics-as-Σ-nested
                                      (agda-editor-tactics-record-info it))
      ) ;; Must be on a new line; I'm using noweb-refs
    
    )) ;; Must be on a new line; I'm using noweb-refs

;; The tactic prodcues a Σ-type, what should its name be?
(defvar agda-editor-tactics-format-Σ-naming "%s′"
"The format string for the new Σ-variant.

The new name of the Σ-variant: By default, if R is the record name,
then R′ is the Σ-variant name.  Another useful naming scheme may be
\"%s-Σ-variant\".")

(defun agda-editor-tactics-indent (s)
  "Determine the current indentiation of the string S.

That is, return the number of whitespace at the start of S."
  (length (car (s-match "\\( \\)+" s))))

(defun agda-editor-tactics-record-info (r)
  "Parse an Agda record R as a Lisp plist.

The resulting plist has the following keys.

:name   The name of the record.

:level  The overall type level of the record type.

:body   The sequence of declarations constituting the record.
        Each declaration is a list (qualifier entry),
        where qualifier is a symbol from:

        :param This entry is in the parameters list.
        :local This is a local declaration.
        :field This entry is a field declaration.

For instance, on the input

   record R (X : Set) (x : X) (y : Y x) : Set where

     w : Set
     w = X

     m = w

     field
       a : X

     b : X
     b = X

     field
       c : Y a

We obtain the following, modulo missing quotes:

   (:name  R
    :level \"\"
    :body ((:param X : Set) (:param x : X) (:param y : Y x)
           (:local w : Set) (:local w = X) (:local m = w)
           (:field a : X)
           (:local b : X) (:local b = X)
           (:field c : Y a)))

For now,
 + The ‘field’ keyword must appear by itself on a line.
 + No ‘{implicit}’ arguments supported; nor telescoping.
 + The ‘private’ keyword for Agda records is not supported."
  (-let* ((((header . preamble) . rest)
             (--split-when (s-contains? "field" it) (s-lines (s-trim r))))
          ((_ lhs lvl)
             (s-match "record \\(.*\\) : Set\\(.*\\) where" header))
          ((nom . parms₀)
             (s-split " " lhs))
          (parms (s-join " " parms₀))
          plist)

    ;; ⟨0⟩ Every parameter is part of the body.
    (mapc (lambda (it) (push (list :param (cl-second it))
                        (cl-getf plist :body)))
          ;; "(x : A) (y : B)    (z : Z x y)"  ↦  ("x : A" "y : B" "z : Z x y")
          (s-match-strings-all "(\\(.*?\\))" parms))

    ;; ⟨1⟩ Every local declaration before the first ‘field’ keyword is part of
    ;; the body
    (mapc (lambda (it) (push (list :local (s-trim it))
                        (cl-getf plist :body)))
          preamble)

    ;; ⟨2⟩ The rest of the body.  Agda allows varying, but consistent,
    ;; indentation levels, so we check indentation case by case.
    (loop for p in rest ;; i.e., p is a chunk of lines immediately after a
                        ;; ‘field’ keyword.
          for indent = (agda-editor-tactics-indent (cl-first p))
          ;; The lines sharing the same indentation are fields,
          ;; everything else is a local definitional extension.
          ;; These claims are true provided
          ;; the record actually typechecks in Agda.
          do (mapc (lambda (it)
                     (push (list (if (= indent (agda-editor-tactics-indent it))
                                     :field
                                   :local)
                                 (s-trim it))
                           (cl-getf plist :body)))
                   p))

    ;; ⟨3⟩ Omit blank lines
    (setf (cl-getf plist :body)
          (--reject (s-blank? (s-trim (cl-second it))) (cl-getf plist :body)))

    ;; ⟨4⟩ Ensure order of :body is params, then everything else.
    (setf (cl-getf plist :body) (reverse (cl-getf plist :body)))

    ;; ⟨5⟩ Register the level and name of the record
    (setf (cl-getf plist :level) lvl)
    (setf (cl-getf plist :name) nom)

    ;; ⟨7⟩ Yield the record as a Lisp plist.
    plist))

(cl-defmacro agda-editor-tactics-regonify
    (f &optional
       (from-string 'it)
       (on-region `(progn
                     (kill-new it)
                     (message "Result of %s is now in your %s"
                              (quote ,f)
                              "clipboard -- press C-y to paste it (•̀ᴗ•́)و"))))
"Given an unary function F, extend it to work interactively on regions.

Override the existing function F to be interactive and to work on
selected regions.  When F is called in Lisp code, it will act as the
orginal function.  When F is called interactively on a selected region
of text, we use the function-body FROM-STRING to prepare the selected
text as appropriate intoput to F, then we act on the region using
the function body ON-REGION.

FROM-STRING is an expression that transforms ‘it’, the input string,
into the approriate datatype required by F.

ON-REGION is an expression involving ‘it’, the output of F,
as well as ‘start’ and ‘end’, the boundaries of the region.

Below is a full example, where the output is pasted over a region.

   (defun myupcase (s)
     \"Shout the string S.\"
     (upcase s))

   (regonify myupcase it (progn (delete-region start end) (insert it)))

Moreover, evaluating a ‘regonify’ sexp multiple times results
“works fine”; i.e., this is an idempotent operation (mostly).
[Each invocation increases the documentation; and more.]"
  `(defun ,f (x &optional start end)
     ,(concat (documentation f)
             "\nWhen invoked interactively, works on the selected region.")
     (interactive (list nil (region-beginning) (region-end)))
     (let* ((input  (or x (funcall (lambda (it) ,from-string)
                                   (buffer-substring-no-properties start end))))
            (output (funcall ,(symbol-function f) input)))
       (if x ;; i.e., not working on a region
           output
         (funcall (lambda (it) ,on-region) output)))))

(defun agda-editor-tactics-as-Σ-nested (r)
  "Transform an Agda record R, as a plist, into an Agda Σ-type."
  (-let* (((paramsPV body) (--split-with (equal :param (cl-first it)) (cl-getf r :body)))
          ;; paramsPV is a list of pairs (:param value).
          (params (mapcar #'cl-second paramsPV))
          (args (--map (s-trim (cl-first (s-split ":" it))) params)))

    (s-concat

     ;; ⟨0⟩ Type declaration
     (format agda-editor-tactics-format-Σ-naming (cl-getf r :name))
     " : "
     (when params (concat (s-join " " (--map (format "(%s)" it) params)) " → "))
     "Set " (cl-getf r :level) "\n"

     ;; ⟨1⟩ Body definition
     (format agda-editor-tactics-format-Σ-naming (cl-getf r :name))
     " = "
     (if (not args)
         ""
       (format "λ %s → " (s-join " " args)))

    ;; Arrange record as a sequence of let-clauses and Σ-quantifiers.
    (thread-last
        (loop for (q e) in body
              for e′ = (if (equal q :field) (s-replace ":" "∶" e) e)
              concat (format (if (equal q :field) "Σ %s • " "let %s in ") e′))
      (s-collapse-whitespace)
      (s-replace "in let" ";")
      (s-replace "; ;"    ";")
      (s-replace "let ;"  "let ")
      (s-replace "; in"   " in"))

     ;; Final element of a Σ-type will be, consistently, the unit type.
      "⊤")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'agda-editor-tactics)

;;; agda-editor-tactics.el ends here
