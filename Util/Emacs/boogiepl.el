;;; boogiepl.el --- BoogiePL major mode

;; Copyright (C) 2009, 2010 Valentin Wüstholz

;; Author: Valentin Wüstholz
;; Keywords: Boogie, BoogiePL, major mode
;; Version: 0.1

;; This file is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License,
;; or (at your option) any later version.
;;
;; This file is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:

;; This is a Emacs mode for BoogiePL. It supports syntax-highlighting,
;; indention and imenu.

;; To install it, you simply have to add the following lines to your .emacs file:

;; (add-to-list 'load-path (expand-file-name "path/to/this/file/"))
;; (require 'boogiepl)
;; (add-to-list 'auto-mode-alist '("\\.bpl$" . boogiepl-mode))


;;; Code:


(require 'imenu)
(require 'easymenu)
(require 'speedbar)


(defvar boogiepl-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [remap comment-dwim] 'boogiepl-comment-dwim)
    (define-key map [return] 'newline-and-indent)
    (define-key map "\C-c\C-c" 'boogiepl-run-boogie)
    map)
  "Keymap for `boogiepl-mode'.")


(defvar boogiepl-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\/  ". 124b" st)
    (modify-syntax-entry ?\*  ". 23n"  st)
    (modify-syntax-entry ?\n  "> b"    st)
    (modify-syntax-entry ?\r  "> b"    st)
    st)
  "Syntax table for `boogiepl-mode'.")


(defun boogiepl-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way.
For detail, see `comment-dwim'."
  (interactive "*P")
  (require 'newcomment)
  (let ((deactivate-mark nil) (comment-start "// ") (comment-end ""))
    (comment-dwim arg)))


(defvar boogiepl-imenu-generic-expression
  '(
    ("Functions"
     "^[:space:]*function *\\([^(\n\s-]+?\\) *(" 1)
    ("Procedures"
     "^[:space:]*procedure *\\([^(\n\s-]+\\) *(" 1)
    ("Implementations"
     "^[:space:]*implementation *\\([^(\n\s-]+\\) *(" 1)
    ("Types"
     "^[:space:]*type *\\([^;\n\s-]+[^\n]*\\);" 1)
    ("Constants"
     "^[:space:]*const *\\(unique\\)? *\\([^;\n\s-]+\\) *:" 2)
    ("Variables"
     "^[:space:]*var *\\([^;\n\s-]+\\):" 1)
    ("Axioms"
     "^[:space:]*axiom *\\([^;]+\\);" 1)
    )
  )


;;; Speedbar

(if (fboundp 'speedbar-add-supported-extension)
    (speedbar-add-supported-extension '(".bpl")))


;;; Menu

(defun boogiepl-menu ()
  (easy-menu-define
    boogiepl-mode-menu
    (list boogiepl-mode-map)
    "BoogiePL Mode Menu"
    '("BoogiePL"
      ["Run Boogie" boogiepl-run-boogie t]
      ["Run Boogie with /smoke" boogiepl-run-boogie-with-smoke t]
      "-"
      ["Indent the marked region or the whole buffer" boogiepl-indent-marked-region-or-buffer t]
      )
    )
  (easy-menu-add boogiepl-mode-menu)
  )


;;; Commands

(defcustom boogiepl-command
  "boogie /nologo"
  "Command-line command to run Boogie"
  :type 'string
  :group 'boogie
  )

(defun boogiepl-run-boogie-with-smoke ()
  "Run Boogie with /smoke."
  (interactive)
  (boogiepl-run-boogie t))

(defun boogiepl-run-boogie (&optional smokep)
  "Run Boogie."
  (interactive)
  (let* ((filename (file-name-nondirectory buffer-file-name))
         (command (format "%s %s %s"
                          boogiepl-command
                          (if smokep "/smoke" "")
                          filename)))
    (compile command)))


;; Define several class of keywords.
(defvar boogiepl-keywords
  '("type" "const" "function" "returns" "axiom" "var" "procedure" "requires" "modifies" "ensures" "implementation" "goto" "return" "assert" "assume" "havoc" "call" "call forall" "finite" "unique" "free" "invariant" "if" "else" "while" "complete" "break" "where" "extends")
  "BoogiePL keywords")

(defvar boogiepl-types
  '("bool" "int" "ref")
  "BoogiePL types")

(defvar boogiepl-constants
  '("true" "false" "null")
  "BoogiePL constants")

(defvar boogiepl-operators
  '("<==>" "==>" "&&" "||" "==" "!=" "<=" ">=" "<" ">" "!" "forall" "exists" "::" "<:")
  "BoogiePL operators")

(defvar boogiepl-functions
  '("old")
  "BoogiePL functions")

;; Create the regex string for each class of keywords.
(defvar boogiepl-keywords-regexp (regexp-opt boogiepl-keywords 'words))
;; (defvar boogiepl-type-regexp (regexp-opt boogiepl-types 'words))
(defvar boogiepl-type-regexp "\\<\\(b\\(?:ool\\|v[0-9]+\\)\\|int\\|ref\\)\\>")
(defvar boogiepl-constant-regexp (regexp-opt boogiepl-constants 'words))
(defvar boogiepl-operators-regexp (regexp-opt boogiepl-operators))
(defvar boogiepl-functions-regexp (regexp-opt boogiepl-functions 'words))

;; Clear memory.
(setq boogiepl-keywords nil)
(setq boogiepl-types nil)
(setq boogiepl-constants nil)
(setq boogiepl-operators nil)
(setq boogiepl-functions nil)

;; Define a face for each keyword class.
(setq boogiepl-font-lock-keywords
      `(
        (,boogiepl-type-regexp . font-lock-type-face)
        (,boogiepl-constant-regexp . font-lock-constant-face)
        (,boogiepl-operators-regexp . font-lock-builtin-face)
        (,boogiepl-functions-regexp . font-lock-function-name-face)
        (,boogiepl-keywords-regexp . font-lock-keyword-face)
        ))


(defcustom boogiepl-mode-hook nil
  "Mode hook for boogiepl-mode, run after the mode was turned on."
  :type 'hook
  :group 'boogie
  )


;;;###autoload
(define-derived-mode boogiepl-mode fundamental-mode "BoogiePL"
  "A major mode for editing BoogiePL files."
  :group 'boogie
  (set (make-local-variable 'paragraph-separate) (concat "^\\s *$\\|" page-delimiter))
  (set (make-local-variable 'paragraph-start) (concat "^\\s *$\\|" page-delimiter))
  (set (make-local-variable 'paragraph-ignore-fill-prefix) t)
  (set (make-local-variable 'comment-start) "// ")
  (set (make-local-variable 'comment-start-skip) "\\(//+\\|/\\*+\\)\\s *")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-end-skip) " *[*]+/")
  (set (make-local-variable 'font-lock-multiline) nil)
  (setq font-lock-defaults '((boogiepl-font-lock-keywords)))
  (set (make-local-variable 'font-lock-defaults)
       '(boogiepl-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'boogiepl-indent-line)
  (set (make-local-variable 'imenu-generic-expression)
       boogiepl-imenu-generic-expression)
  (set (make-local-variable 'compile-command) (format "%s %s"
                                                      boogiepl-command
                                                      (file-name-nondirectory buffer-file-name)))
  ;; Clear memory.
  (setq boogiepl-keywords-regexp nil)
  (setq boogiepl-types-regexp nil)
  (setq boogiepl-constants-regexp nil)
  (setq boogiepl-operators-regexp nil)
  (setq boogiepl-functions-regexp nil)
  (turn-on-font-lock)
  (jit-lock-fontify-now)
  (boogiepl-menu)
  (imenu-add-menubar-index)
  (imenu-update-menubar)
  (run-mode-hooks 'boogiepl-mode-hook)
  )


;;; Indentation

(defun boogiepl-indent-line ()
  "Indent current line of BoogiePL code."
  (interactive)
  (let* ((savep (point))
         (indent (condition-case nil
                     (save-excursion
                       (forward-line 0)
                       (skip-chars-forward " \t")
                       (if (>= (point) savep) (setq savep nil))
                       (max (boogiepl-calculate-indentation) 0))
                   (error 0))))
    (if savep
        (save-excursion (indent-line-to indent))
      (indent-line-to indent))))

(defun looking-at-comment ()
  (and font-lock-mode
       (or (looking-at "/[*]+ *\\|//+ *")
           (eq (get-text-property (point) 'face) 'font-lock-comment-face)))
  )

(defun boogiepl-calculate-indentation ()
  "Return the column to which the current line should be indented."
  (cond ((looking-at-comment)  ; comments
         (current-indentation))
        ((looking-at "[^\n\s-]+\\s-*:\\s-*$")  ; label
         2)
        ((and font-lock-mode (eq (get-text-property (point) 'face) 'font-lock-builtin-face))  ; operators
         (current-indentation))
        ((looking-at "\\(free +\\)?\\(requires\\|modifies\\|ensures\\)")  ; specification
         2)
        (t
         (let ((cur-indent 0))
           (if (looking-at "}.*")
               (incf cur-indent -4))
           (while (and (not (bobp)) (not (looking-at "\\s-*\\(implementation\\|function\\|procedure\\|const\\|axiom\\|type\\)")))
             (forward-line -1)
             (unless (looking-at-comment)
               (if (looking-at ".*{.*")
                   (incf cur-indent 4))
               (if (looking-at ".*}.*")
                   (incf cur-indent -4))
               )
             )
           cur-indent)
         )
        )
  )

(defun boogiepl-indent-marked-region-or-buffer ()
  "Indent the marked region or the whole buffer."
  (interactive)
  (save-excursion
    (if (not mark-active)
        (mark-whole-buffer))
    (call-interactively 'untabify)
    (call-interactively 'indent-region))
  )


(provide 'boogiepl)

;;; boogiepl.el ends here
