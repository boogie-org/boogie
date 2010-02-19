;;; flymake-boogiepl.el --- Flymake BoogiePL Extension

;; Copyright (C) 2009, 2010 Valentin Wüstholz

;; Author: Valentin Wüstholz
;; Keywords: flymake, Boogie, BoogiePL
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

;; This is a Flymake extension for BoogiePL.

;; To install it, you simply have to add the following lines to your .emacs file:

;; (add-to-list 'load-path (expand-file-name "path/to/this/file/"))
;; (require 'flymake-boogiepl)
;; (require 'boogiepl)                                                    ; optional
;; (define-key boogiepl-mode-map (kbd "C-c p") 'flymake-goto-prev-error)  ; optional
;; (define-key boogiepl-mode-map (kbd "C-c n") 'flymake-goto-next-error)  ; optional


;;; Code:


(require 'flymake)


(defcustom flymake-boogiepl-command
  "boogie"
  "Command to run Boogie"
  :type 'string
  :group 'boogie
  )

(defcustom flymake-boogiepl-prelude-files
  nil
  "Prelude files"
  :group 'boogie
  )

(defcustom flymake-boogiepl-flags
  (list "/nologo" "/smoke")
  "Flags"
  :group 'boogie
  )


(defun flymake-boogiepl-init ()
  (let* ((temp-file         (flymake-init-create-temp-buffer-copy
                             'flymake-create-temp-inplace))
         (local-file        (file-relative-name
                             temp-file
                             (file-name-directory buffer-file-name)))
         (files             (if (not (member (file-relative-name (buffer-file-name))
                                             flymake-boogiepl-prelude-files))
                                (cons local-file flymake-boogiepl-prelude-files)
                              flymake-boogiepl-prelude-files)))
    (list flymake-boogiepl-command (append flymake-boogiepl-flags files))))


(defvar flymake-boogiepl-err-line-patterns '(("^\\(.*\.bpl\\)(\\([0-9]+\\),\\([0-9]+\\)): Error\\( \\S-*\\)?: \\(.*\\)$" 1 2 3 5)
                                             ("^\\(.*\.bpl\\)(\\([0-9]+\\),\\([0-9]+\\)): Related location: \\(.*\\)$" 1 2 3 4)
                                             ("^    \\(.*\.bpl\\)(\\([0-9]+\\),\\([0-9]+\\)): \\(.*\\)$" 1 2 3 4)
                                             ("^\\(.*\.bpl\\)(\\([0-9]+\\),\\([0-9]+\\)): syntax error: \\(.*\\)$" 1 2 3 4)
                                             ("^\\(found unreachable code\\):$" nil nil nil 1)))

(defvar flymake-boogiepl-allowed-file-name-masks '(("\\.bpl\\'" flymake-boogiepl-init)))


(setq flymake-allowed-file-name-masks
      (append flymake-boogiepl-allowed-file-name-masks
              flymake-allowed-file-name-masks))

(setq flymake-err-line-patterns
      (append flymake-boogiepl-err-line-patterns
              flymake-err-line-patterns))


(provide 'flymake-boogiepl)

;;; flymake-boogiepl.el ends here
