;; chalice-mode.el - GNU Emacs mode for Chalice
;; Adapted by Rustan Leino from Jean-Christophe FILLIATRE's GNU Emancs mode for Why

(defvar chalice-mode-hook nil)

(defvar chalice-mode-map nil
  "Keymap for Chalice major mode")

(if chalice-mode-map nil
  (setq chalice-mode-map (make-keymap))
  (define-key chalice-mode-map "\C-c\C-c" 'chalice-run-boogie)
  (define-key chalice-mode-map [(control return)] 'font-lock-fontify-buffer))

(setq auto-mode-alist
      (append
       '(("\\.chalice" . chalice-mode))
       auto-mode-alist))

;; font-lock

(defun chalice-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst chalice-font-lock-keywords-1
  (list
   ; comments have the form /* ... */
   '("/\\*\\([^*]\\|\\*[^/]\\)*\\*/" . font-lock-comment-face)
   ; or // ...
   '("//\\([^
]\\)*" . font-lock-comment-face)

   `(,(chalice-regexp-opt '(
        "class" "ghost" "var" "const" "external" "function" "method"
        "predicate" "returns" "requires" "ensures" "lockchange"
        "invariant" "channel" "condition" "where"
        "refines" "transforms"
        )) . font-lock-builtin-face)
   `(,(chalice-regexp-opt '(
        "above" "acc" "acquire" "and" "assert" "assigned" "assume"
        "below" "between" "call" "credit"
        "downgrade" "else" "eval" "exists" "fold" "forall" "fork" "free" "havoc" "holds"
        "spec" "replaces" "by"
        "if" "in" "ite" "join" "lock" "lockbottom" "waitlevel" "module" "new" "nil"
        "old" "rd" "receive" "release" "reorder" "result" "send" "share"
        "this" "unfold" "unfolding" "unshare" "while"
        "false" "true" "null")) . font-lock-keyword-face)
   `(,(chalice-regexp-opt '("bool" "int" "seq" "token")) . font-lock-type-face)
   )
  "Minimal highlighting for Chalice mode")

(defvar chalice-font-lock-keywords chalice-font-lock-keywords-1
  "Default highlighting for Chalice mode")

;; syntax

(defvar chalice-mode-syntax-table nil
  "Syntax table for chalice-mode")

(defun chalice-create-syntax-table ()
  (if chalice-mode-syntax-table
      ()
    (setq chalice-mode-syntax-table (make-syntax-table))
    (set-syntax-table chalice-mode-syntax-table)
    (modify-syntax-entry ?' "w" chalice-mode-syntax-table)
    (modify-syntax-entry ?_ "w" chalice-mode-syntax-table)))

;; menu

(require 'easymenu)

(defun chalice-menu ()
  (easy-menu-define
   chalice-mode-menu (list chalice-mode-map)
   "Chalice Mode Menu." 
   '("Chalice"
     ["Run Boogie" chalice-run-boogie t]
     "---"
     ["Recolor buffer" font-lock-fontify-buffer t]
     "---"
     ))
  (easy-menu-add chalice-mode-menu))

;; commands

(defun chalice-command-line (file)
  (concat "boogie " file))

(defun chalice-run-boogie ()
  "run Boogie to check the Chalice program"
  (interactive)
  (let ((f (buffer-name)))
    (compile (chalice-command-line f))))

;; setting the mode

(defun chalice-mode ()
  "Major mode for editing Chalice programs.

\\{chalice-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (chalice-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(chalice-font-lock-keywords))
  ; indentation
  ; (make-local-variable 'indent-line-function)
  ; (setq indent-line-function 'chalice-indent-line)
  ; menu
  ; providing the mode
  (setq major-mode 'chalice-mode)
  (setq mode-name "Chalice")
  (use-local-map chalice-mode-map)
  (font-lock-mode 1)
  (chalice-menu)
  (run-hooks 'chalice-mode-hook))

(provide 'chalice-mode)
