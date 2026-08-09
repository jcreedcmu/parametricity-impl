;;; tt-mode.el --- Major mode for two-level parametricity .tt files -*- lexical-binding: t; -*-

;; Author: parametricity
;; Keywords: languages
;; Version: 0.1

;;; Commentary:

;; Basic font-lock for the surface syntax of the glue/fiber two-level type
;; theory checker (see GENERALIZATION_PLAN.md). Highlights keywords, the
;; universe `U', the hypothesis-kind markers `:' `:-' `::', arrows, `let'-bound
;; names, and `--' / `{- -}' comments.
;;
;; Usage:
;;   (add-to-list 'load-path "/path/to/parametricity/etc")
;;   (require 'tt-mode)
;; `.tt' files then open in `tt-mode' automatically.

;;; Code:

(defvar tt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; `--' line comments and `{- -}' block comments (Haskell-style).
    (modify-syntax-entry ?\{ "(}1nb" st)
    (modify-syntax-entry ?\} "){4nb" st)
    (modify-syntax-entry ?-  ". 123" st)
    (modify-syntax-entry ?\n ">" st)
    ;; Bracket pairs.
    (modify-syntax-entry ?\[ "(]" st)
    (modify-syntax-entry ?\] ")[" st)
    ;; Punctuation (so they don't glue onto identifiers as symbol constituents).
    (modify-syntax-entry ?:  "." st)
    (modify-syntax-entry ?=  "." st)
    (modify-syntax-entry ?,  "." st)
    (modify-syntax-entry ?.  "." st)
    (modify-syntax-entry ?\\ "." st)
    st)
  "Syntax table for `tt-mode'.")

(defconst tt-mode-keywords
  '("let" "in" "with" "Glue" "glue" "unglue" "fib" "unfib")
  "Keywords of the .tt surface language.")

(defvar tt-mode-font-lock-keywords
  `( ;; Reserved words.
    (,(regexp-opt tt-mode-keywords 'symbols) . font-lock-keyword-face)
    ;; The universe.
    ("\\_<U\\_>" . font-lock-builtin-face)
    ;; Lambda (both spellings).
    ("[λ\\]" . font-lock-keyword-face)
    ;; The name bound by `let'.
    ("\\_<let\\_>[[:space:]]+\\([A-Za-z0-9_']+\\)" 1 font-lock-function-name-face)
    ;; Hypothesis-kind markers `::' (strong) and `:-' (weak), before a lone `:'.
    ("::\\|:-" . font-lock-type-face)
    ;; Arrows.
    ("->\\|→" . font-lock-type-face))
  "Font-lock rules for `tt-mode'.")

;;;###autoload
(define-derived-mode tt-mode prog-mode "TT"
  "Major mode for editing two-level parametricity .tt files."
  :syntax-table tt-mode-syntax-table
  (setq-local comment-start "-- ")
  (setq-local comment-end "")
  (setq-local comment-start-skip "\\(?:--+\\|{-\\)[ \t]*")
  (setq-local font-lock-defaults '(tt-mode-font-lock-keywords))
  (setq-local font-lock-keywords-case-fold-search nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tt\\'" . tt-mode))

(define-key tt-mode-map (kbd "C-c C-t") #'tt-browse-tests)


;;; Test browser --------------------------------------------------------------

;; `tt-browse-tests' opens a left-hand panel listing every `.tt' file under the
;; project's `tests/' directory. Selecting one shows the test (top-right) beside
;; its `.golden' (bottom-right).

(defvar tt-tests-panel-width 64
  "Width, in columns, of the `tt-browse-tests' panel.")

(defvar-local tt--tests-dir nil
  "Root `tests/' directory backing this browser buffer.")

(defvar-local tt--test-count 0
  "Number of tests listed in this browser buffer.")

(defvar-local tt--tt-window nil
  "Window this panel reuses to show the selected `.tt' file.")

(defvar-local tt--golden-window nil
  "Window this panel reuses to show the selected `.golden' file.")

(defvar-local tt--output-window nil
  "Window this panel reuses to show the selected test's runner output.")

(defvar-local tt--test-status nil
  "Hash table mapping a test's absolute path to its last run status.
Values are the symbols `pass', `fail', or `nogold'; nil before any run.")

(defvar-local tt--test-output nil
  "Hash table mapping a test's absolute path to its last run output block.
Each value is the runner's text for that test (the `FAIL' diff, etc.).")

(defvar tt-run-tests-command "lake exe test"
  "Shell command `tt-run-tests' runs, from the directory that contains `tests/'.
It is expected to print one `PASS'/`FAIL'/`NOGOLD' line per test naming the test
file, as the runner in `Parametricity/TestRunner.lean' does. Note this inherits
Emacs's environment; set it to an absolute path or a wrapper if `lake' is not on
`exec-path'.")

(defface tt-test-pass '((t :inherit success))
  "Face for a passing test in the `tt-browse-tests' panel.")

(defface tt-test-fail '((t :inherit error))
  "Face for a failing test in the `tt-browse-tests' panel.")

(defface tt-test-nogold '((t :inherit warning))
  "Face for a test with no golden file in the `tt-browse-tests' panel.")

(defun tt--find-tests-dir ()
  "Return the project's `tests/' directory, or nil if none is found.
Prefer a `tests' subdirectory of `default-directory'; otherwise walk up the
current path looking for a component named `tests'."
  (let ((sub (expand-file-name "tests" default-directory)))
    (if (file-directory-p sub)
        (file-name-as-directory sub)
      (let ((dir (directory-file-name (expand-file-name default-directory)))
            (result nil))
        (while (and (not result)
                    (not (string-equal dir (directory-file-name
                                            (file-name-directory dir)))))
          (if (string-equal (file-name-nondirectory dir) "tests")
              (setq result (file-name-as-directory dir))
            (setq dir (directory-file-name (file-name-directory dir)))))
        result))))

(defun tt--missing-golden-buffer (golden)
  "Return a read-only buffer noting that GOLDEN does not exist."
  (let ((buf (get-buffer-create "*tt-no-golden*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert (format "No golden file:\n\n  %s\n" golden)))
      (setq buffer-read-only t))
    buf))

(defun tt--status-face (status)
  "Return the panel face for run STATUS, or nil."
  (pcase status
    ('pass 'tt-test-pass)
    ('fail 'tt-test-fail)
    ('nogold 'tt-test-nogold)
    (_ nil)))

(defun tt--fill-list (buf dir)
  "Fill BUF with the `.tt' files under DIR, colored by `tt--test-status'.
Assumes BUF is already in `tt-tests-mode'. Preserves the current line."
  (with-current-buffer buf
    (let ((inhibit-read-only t)
          (files (sort (directory-files-recursively dir "\\.tt\\'") #'string<))
          (line (line-number-at-pos)))
      (erase-buffer)
      (dolist (f files)
        (let ((face (tt--status-face (and tt--test-status
                                          (gethash f tt--test-status))))
              (beg (point)))
          (insert (propertize (file-relative-name f dir) 'tt-file f))
          (when face (add-text-properties beg (point) (list 'face face)))
          (insert "\n")))
      (setq tt--tests-dir dir
            tt--test-count (length files))
      (goto-char (point-min))
      (forward-line (1- line)))
    buf))

(defun tt--join-block (lines)
  "Join LINES into one newline-terminated string, dropping trailing blank lines."
  (let ((ls lines))
    (while (and ls (string-match-p "\\`[ \t]*\\'" (car (last ls))))
      (setq ls (butlast ls)))
    (concat (mapconcat #'identity ls "\n") "\n")))

(defun tt--decorate-output ()
  "Color the current output buffer: the status word and the diff markers."
  (save-excursion
    (goto-char (point-min))
    (when (looking-at "\\(PASS\\|FAIL\\|NOGOLD\\)\\_>")
      (let ((face (tt--status-face (pcase (match-string 1)
                                     ("PASS" 'pass) ("FAIL" 'fail) ("NOGOLD" 'nogold)))))
        (when face
          (add-text-properties (line-beginning-position) (line-end-position)
                               (list 'face face)))))
    (while (re-search-forward "^[ \t]*--- \\(?:expected\\|actual\\) ---[ \t]*$" nil t)
      (add-text-properties (line-beginning-position) (line-end-position)
                           '(face bold)))))

(defun tt--output-buffer (text)
  "Return the shared `*tt-output*' buffer showing TEXT (or a placeholder)."
  (let ((buf (get-buffer-create "*tt-output*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert (or text "No test output. Run `tt-run-tests' (t) in the panel.\n"))
        (tt--decorate-output))
      (goto-char (point-min))
      (setq buffer-read-only t))
    buf))

(defvar tt-tests-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET")   #'tt-tests-visit)
    (define-key map [mouse-1]     #'tt-tests-mouse-visit)
    (define-key map (kbd "g")     #'tt-tests-refresh)
    (define-key map (kbd "t")     #'tt-run-tests)
    map)
  "Keymap for `tt-tests-mode'.")

(define-derived-mode tt-tests-mode special-mode "TT-Tests"
  "Major mode for the `tt-browse-tests' panel.
\\{tt-tests-mode-map}"
  (hl-line-mode 1))

(defun tt-tests-visit ()
  "Open the test on the current line, its `.golden', and its last run output.
The `.tt' goes top-right, the `.golden' middle-right, and the runner output
bottom-right."
  (interactive)
  (let ((file (get-text-property (line-beginning-position) 'tt-file)))
    (unless file (user-error "No test file on this line"))
    (let* ((golden (concat file ".golden"))
           (tt-buf (find-file-noselect file))
           (golden-buf (if (file-exists-p golden)
                           (find-file-noselect golden)
                         (tt--missing-golden-buffer golden)))
           (out-buf (tt--output-buffer (and tt--test-output
                                            (gethash file tt--test-output))))
           (list-win (selected-window)))
      (if (and (window-live-p tt--tt-window)
               (window-live-p tt--golden-window)
               (window-live-p tt--output-window)
               (eq (window-frame tt--tt-window) (window-frame list-win))
               (eq (window-frame tt--golden-window) (window-frame list-win))
               (eq (window-frame tt--output-window) (window-frame list-win)))
          ;; Reuse the existing split: just swap the buffers in place.
          (progn
            (set-window-buffer tt--tt-window tt-buf)
            (set-window-buffer tt--golden-window golden-buf)
            (set-window-buffer tt--output-window out-buf))
        ;; Otherwise (re)build the layout and remember its windows.
        (delete-other-windows list-win)
        (let* ((tt-win     (split-window list-win tt-tests-panel-width 'right))
               (golden-win (split-window tt-win nil 'below))
               (out-win    (split-window golden-win nil 'below)))
          (set-window-buffer tt-win tt-buf)
          (set-window-buffer golden-win golden-buf)
          (set-window-buffer out-win out-buf)
          (setq tt--tt-window tt-win
                tt--golden-window golden-win
                tt--output-window out-win)))
      (select-window list-win))))

(defun tt-tests-mouse-visit (event)
  "Select the clicked test line (EVENT) and visit it."
  (interactive "e")
  (mouse-set-point event)
  (tt-tests-visit))

(defun tt-tests-refresh ()
  "Re-scan the tests directory backing this panel (keeping run colors)."
  (interactive)
  (unless tt--tests-dir (user-error "Not in a tt-browse-tests panel"))
  (tt--fill-list (current-buffer) tt--tests-dir)
  (message "Refreshed: %d tests" tt--test-count))

(defun tt--project-root (dir)
  "Directory that contains the tests directory DIR (where the runner is run)."
  (file-name-directory (directory-file-name dir)))

;;;###autoload
(defun tt-run-tests ()
  "Run the test suite and color the `tt-browse-tests' panel by pass/fail.
Run `tt-run-tests-command' in the directory that contains `tests/', parse its
`PASS'/`FAIL'/`NOGOLD' lines, and recolor each test: passing green
\(`tt-test-pass'), failing red (`tt-test-fail'), and tests with no golden
`tt-test-nogold'. Each test's output block (the `FAIL' diff, etc.) is stored
and shown in the bottom-right pane when you select that test. Works from the
panel, or from anywhere once the panel exists."
  (interactive)
  (let ((buf (if (and tt--tests-dir (derived-mode-p 'tt-tests-mode))
                 (current-buffer)
               (get-buffer "*tt-tests*"))))
    (unless (and buf (buffer-local-value 'tt--tests-dir buf))
      (user-error "Run `tt-browse-tests' first"))
    (let* ((dir (buffer-local-value 'tt--tests-dir buf))
           (root (tt--project-root dir))
           (status (make-hash-table :test 'equal))
           (outputs (make-hash-table :test 'equal))
           (pass 0) (fail 0) (nogold 0)
           (cur nil) (acc nil)          ; current test's abs path and reversed lines
           output)
      (message "Running %s ..." tt-run-tests-command)
      (let ((default-directory root))
        (setq output (shell-command-to-string tt-run-tests-command)))
      ;; Parse per-test blocks.
      (dolist (line (split-string output "\n"))
        (cond
         ((string-match "\\`\\(PASS\\|FAIL\\|NOGOLD\\)[ \t]+\\([^ \t]+\\)" line)
          (when cur (puthash cur (tt--join-block (nreverse acc)) outputs))
          (let ((sym (pcase (match-string 1 line)
                       ("PASS" 'pass) ("FAIL" 'fail) ("NOGOLD" 'nogold)))
                (abs (expand-file-name (match-string 2 line) root)))
            (puthash abs sym status)
            (pcase sym
              ('pass   (setq pass   (1+ pass)))
              ('fail   (setq fail   (1+ fail)))
              ('nogold (setq nogold (1+ nogold))))
            (setq cur abs acc (list line))))
         ((string-match-p "\\`[0-9]+ passed" line)   ; final summary ends the block
          (when cur (puthash cur (tt--join-block (nreverse acc)) outputs))
          (setq cur nil acc nil))
         (cur (push line acc))))                     ; any other line continues it
      (when cur (puthash cur (tt--join-block (nreverse acc)) outputs))
      (with-current-buffer buf
        (setq tt--test-status status
              tt--test-output outputs)
        (tt--fill-list buf dir))
      (message "Tests: %d passed, %d failed%s"
               pass fail
               (if (> nogold 0) (format ", %d without goldens" nogold) "")))))

;;;###autoload
(defun tt-browse-tests ()
  "Browse the project's `tests/' tree in a left-hand panel.
Locate `tests/' either as a subdirectory of the current directory or as an
ancestor component of it, list every `.tt' file under it recursively, and show
the list in a panel on the left of the frame. Press RET (or `mouse-1') on a
test to open the `.tt' (top-right), its `.golden' (middle-right), and its last
run output (bottom-right). Use `tt-run-tests' (\\`t') to color the list by
pass/fail and populate the output pane."
  (interactive)
  (let ((dir (tt--find-tests-dir)))
    (unless dir
      (user-error "Cannot find a `tests/' directory here"))
    (let ((buf (get-buffer-create "*tt-tests*")))
      (with-current-buffer buf
        (unless (derived-mode-p 'tt-tests-mode) (tt-tests-mode)))
      (tt--fill-list buf dir)
      (delete-other-windows)
      (let ((list-win (selected-window)))
        (split-window list-win tt-tests-panel-width 'right)
        (set-window-buffer list-win buf)
        (select-window list-win))
      (message "tt-browse-tests: %d test%s under %s"
               (buffer-local-value 'tt--test-count buf)
               (if (= (buffer-local-value 'tt--test-count buf) 1) "" "s")
               (abbreviate-file-name dir)))))

(provide 'tt-mode)
;;; tt-mode.el ends here
