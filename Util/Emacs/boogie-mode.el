;; boogie-mode.el - GNU Emacs mode for Boogie 2
;; Adapted by Rustan Leino from Jean-Christophe FILLIATRE's GNU Emancs mode for Why

(defvar boogie-mode-hook nil)

(defvar boogie-mode-map nil
  "Keymap for Boogie major mode")

(if boogie-mode-map nil
  (setq boogie-mode-map (make-keymap))
  (define-key boogie-mode-map "\C-c\C-c" 'boogie-run-boogie)
  (define-key boogie-mode-map [(control return)] 'font-lock-fontify-buffer))

(setq auto-mode-alist
      (append
       '(("\\.bpl" . boogie-mode))
       auto-mode-alist))

;; font-lock

(defun boogie-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst boogie-font-lock-keywords-1
  (list
   ; comments have the form /* ... */
   '("/\\*\\([^*]\\|\\*[^/]\\)*\\*/" . font-lock-comment-face)
   ; or // ...
   '("//[^\r\n]*" . font-lock-comment-face)
   `(,(boogie-regexp-opt '(
        "type" "const" "function" "axiom" "var" "procedure" "implementation"
        "returns" "where" "requires" "ensures" "modifies" "free" "unique"
        "invariant" "extends" "complete"
        )) . font-lock-keyword-face)
   `(,(boogie-regexp-opt '(
        "assert" "assume" "break" "call" "then" "else" "havoc" "if" "goto" "return" "while"
        "old" "forall" "exists" "lambda" "cast" "div" "mod"
        )) . font-lock-keyword-face)
   `(,(boogie-regexp-opt '(
        "builtin" "inline" "datatype" "constructor"
        )) . font-lock-preprocessor-face)
   ;; CIVL stuff
   `(,(boogie-regexp-opt '(
        "async" "par"
        )) . font-lock-keyword-face)
   `(,(boogie-regexp-opt '(
        "layer" "yields" "yield_assert"
        "atomic" "left" "right" "both"
        "linear" "linear_in" "linear_out"
        "yield"
        )) . font-lock-preprocessor-face)
   `(,(boogie-regexp-opt '(
        "false" "true"
        )) . font-lock-constant-face)
   `(,(boogie-regexp-opt '(
        "bool" "int" "real"
        "bv0" "bv1" "bv2" "bv3" "bv4" "bv5" "bv6" "bv7" "bv8" "bv9"
        "bv10" "bv11" "bv12" "bv13" "bv14" "bv15" "bv16" "bv17" "bv18" "bv19"
        "bv20" "bv21" "bv22" "bv23" "bv24" "bv25" "bv26" "bv27" "bv28" "bv29"
        "bv30" "bv31" "bv32" "bv33" "bv34" "bv35" "bv36" "bv37" "bv38" "bv39"
        "bv40" "bv41" "bv42" "bv43" "bv44" "bv45" "bv46" "bv47" "bv48" "bv49"
        "bv50" "bv51" "bv52" "bv53" "bv54" "bv55" "bv56" "bv57" "bv58" "bv59"
        "bv60" "bv61" "bv62" "bv63" "bv64" ; and so on
        )) . font-lock-type-face)
   )
  "Minimal highlighting for Boogie mode")

(defvar boogie-font-lock-keywords boogie-font-lock-keywords-1
  "Default highlighting for Boogie mode")

;; syntax

(defvar boogie-mode-syntax-table nil
  "Syntax table for boogie-mode")

(defun boogie-create-syntax-table ()
  (if boogie-mode-syntax-table
      ()
    (setq boogie-mode-syntax-table (make-syntax-table))
    (set-syntax-table boogie-mode-syntax-table)
    (modify-syntax-entry ?' "w" boogie-mode-syntax-table)
    (modify-syntax-entry ?_ "w" boogie-mode-syntax-table)))

;; menu

(require 'easymenu)

(defun boogie-menu ()
  (easy-menu-define
   boogie-mode-menu (list boogie-mode-map)
   "Boogie Mode Menu." 
   '("Boogie"
     ["Run Boogie" boogie-run-boogie t]
     "---"
     ["Recolor buffer" font-lock-fontify-buffer t]
     "---"
     ))
  (easy-menu-add boogie-mode-menu))

;; commands

(defun boogie-command-line (file)
  (concat "boogie -nologo -abbrevOutput " file))

(defun boogie-run-boogie ()
  "run Boogie to check the Boogie program"
  (interactive)
  (let ((f (buffer-name)))
    (compile (boogie-command-line f))))

;; setting the mode

(defun boogie-mode ()
  "Major mode for editing Boogie programs.

\\{boogie-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (boogie-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(boogie-font-lock-keywords))
  ; indentation
  ; (make-local-variable 'indent-line-function)
  ; (setq indent-line-function 'boogie-indent-line)
  (setq-local tab-width 2)
  ; menu
  ; providing the mode
  (setq major-mode 'boogie-mode)
  (setq mode-name "Boogie")
  (use-local-map boogie-mode-map)
  (font-lock-mode 1)
  (boogie-menu)
  (run-hooks 'boogie-mode-hook))

(provide 'boogie-mode)
