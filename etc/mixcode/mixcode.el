(require 'go-mode)

(defvar mixcode-source-dir  nil)
(defvar mixcode-source-file nil)
(defvar mixcode-source-strs nil)
(defvar mixcode-source-tbl  nil)

;;; Note on use with company-coq: The code-inlining feature of mixcode can go
;;; wrong in some cases (e.g., when the struct being inlined contains a map)
;;; with the smart-subscripts feature of company-coq. The ad-hoc fix is to
;;; disable smart-subscripts of company-coq.
;;;
;;; (setq company-coq-disabled-features '(smart-subscripts))

;;; Fontification

(defun mixcode-fontify-source-string (str)
  (with-temp-buffer
	(insert str)
	(go-mode)
	(font-lock-fontify-buffer)
	(buffer-string)))

(defun mixcode-fontify-body (body)
  (let ((vbar (propertize "┃" 'face 'font-lock-comment-face)))
	(format "%s %s"
			vbar
			(mixcode-fontify-source-string (string-trim body "" " *")))))

(defun mixcode-fontify-boundary (str)
  (propertize str 'face 'font-lock-comment-face))

(defun mixcode-fontify-header (header)
  (let* (;; 2 spaces at front, 1 ┏, 2 spaces around `header'
		 (width (- fill-column 2 1 2))
		 (lenheader  (length header))
		 (lenprefix  (max 0 (/ (- width lenheader) 2)))
		 (lenpostfix (max 0 (- width lenprefix lenheader)))
		 (prefix  (mixcode-fontify-boundary (concat "┏" (make-string lenprefix ?━))))
		 (postfix (mixcode-fontify-boundary (make-string lenpostfix ?━))))
	(format "%s %s %s"
			prefix
			(mixcode-fontify-source-string header)
			postfix)))

(defun mixcode-fontify-res-sep (res)
  (let* (;; 4 spaces at front, 1 ┏,1 , 2 spaces around `res'
		 (width (- fill-column 4 1 1 2))
		 (lenres     (length res))
		 (lenprefix  (max 0 (/ (- width lenres) 2)))
		 (lenpostfix (max 0 (- width lenprefix lenres)))
		 (prefix  (mixcode-fontify-boundary (concat "─" (make-string lenprefix ?─))))
		 (postfix (mixcode-fontify-boundary (concat (make-string lenpostfix ?─) "─"))))
	(format "%s %s %s"
			prefix
			(mixcode-fontify-source-string res)
			postfix)))

(defun mixcode-fontify-empty-line ()
  (propertize (format "┖%s" (make-string (- fill-column 2 1) ?╌)) 'face 'font-lock-comment-face))

(defun mixcode-fontify-end-line ()
  (propertize (format "┗%s" (make-string (- fill-column 2 1) ?━)) 'face 'font-lock-comment-face))

(defun mixcode-fontify-buffer ()
  (let ((keywords '(("(\\*@     \\(.*\\) @\\*)"
					 0
					 `(face
					   nil
					   display
					   ;; fontify the first match subexpression
					   ;; (i.e., inside comment notation)
					   ,(mixcode-fontify-body (match-string 1)))
					 ;; set `override' to override major mode fontification
					 t)
					("(\\*@ \\(func .*\\) { +@\\*)"
					 0
					 `(face
					   nil
					   display
					   ,(mixcode-fontify-header (match-string 1)))
					 t)
					("(\\*@ \\(type .*\\) { +@\\*)"
					 0
					 `(face
					   nil
					   display
					   ,(mixcode-fontify-header (match-string 1)))
					 t)
					("(\\*@ } +@\\*)"
					 0
					 `(face
					   nil
					   display
					   ,(mixcode-fontify-end-line))
					 t)
					("(\\*@ Res: \\(.*\\) @\\*)"
					 0
					 `(face
					   nil
					   display
					   ,(mixcode-fontify-res-sep (string-trim (match-string 1))))
					 t)
					("(\\*@ +@\\*)"
					 0
					 `(face
					   nil
					   display
					   ,(mixcode-fontify-empty-line))
					 t))))
	;; TODO: set `'font-lock-extra-managed-props' for resetting fontification
	(font-lock-add-keywords nil keywords)
	(font-lock-fontify-buffer)))

;;; Comment generation

;; (adapted from https://stackoverflow.com/a/44908362)
(defun mixcode-parse-line-numbers (str)
  "Parse string STR representing a range of integers into a list of integers."
  (let (start ranges)
    (while (string-match "\\([0-9]+\\)\\(?:-\\([0-9]+\\)\\)?" str start)
      (push
       (apply 'number-sequence
              (seq-map 'string-to-number
                       (seq-filter
                        'identity
                        (list (match-string 1 str) (match-string 2 str)))))
       ranges)
      (setq start (match-end 0)))
    (nreverse (seq-mapcat 'nreverse ranges))))

(defun mixcode-insert-qed ()
  (insert "Qed.\n"))

(defun mixcode-insert-admitted ()
  (insert "Admitted.\n"))

(defun mixcode-insert-lines (lines)
  (dolist (line lines nil)
	(let ((str (mixcode-source-str-at line)))
	  (when str (insert (format "(\*@ %-71s @\*)\n" str))))))

(defun mixcode-insert-sep ()
  (interactive)
  (insert (format "(\*@ %s @\*)" (make-string 71 ? ))))

(defun mixcode-insert-res-sep (str)
  (interactive "sResources about: ")
  (insert (format "(\*@ Res: %-66s @\*)" str)))

(defun mixcode-insert-code-with-numbers (str)
  "Insert commented code based on line numbers STR."
  (interactive
   (list (progn
		   (unless mixcode-source-strs (error "Run `mixcode-load-file' first."))
		   (read-string "Line numbers (example: 3,5-10): "))))
  (let ((lines (mixcode-parse-line-numbers str)))
	(mixcode-insert-lines lines)))

(defun mixcode-insert-code (sig)
  "Insert commented code based on function signature FUNC."
  (interactive
   (list (progn
		   (unless mixcode-source-strs (error "Run `mixcode-load-file' first."))
		   (completing-read "Function or type name: " mixcode-source-tbl))))
  (let ((range (gethash sig mixcode-source-tbl)))
	(unless range (error "Unknown function name."))
	(let ((begin (point)))
	  (mixcode-insert-lines (number-sequence (car range) (cdr range)))
	  (indent-region begin (point)))))

(defun mixcode-is-func (key value)
  (string-match "^func" key))

(defun mixcode-insert-wp (sig)
  "Insert wp theorem."
  (interactive
   (list (progn
		   (unless mixcode-source-strs (error "Run `mixcode-load-file' first."))
		   (completing-read "Function name: "
							mixcode-source-tbl
							'mixcode-is-func))))
  (let ((range (gethash sig mixcode-source-tbl)))
	(unless range (error "Unknown function name."))
	(mixcode-insert-theorem sig)
	(let ((begin (point)))
	  (mixcode-insert-lines (number-sequence (car range) (cdr range)))
	  (indent-region begin (point)))
	(mixcode-insert-admitted)))

;;; Load and process source file

(defun mixcode-build-tbl ()
  (goto-char (point-min))
  (let ((tbl (make-hash-table :test 'equal)))
	(while (search-forward-regexp "\\(^func .*\\|^type .* struct\\) {" nil t)
	  (let ((func  (string-trim (match-string 1)))
			(begin (line-number-at-pos)))
		(when (search-forward-regexp "^}" nil t)
		  (puthash func (cons begin (line-number-at-pos)) tbl))))
	tbl))

(defun mixcode-build-strs (fname)
  (let ((built (with-temp-buffer
				 (insert-file-contents fname)
				 (goto-char (point-min))
				 ;; replace tab with 4 spaces
				 (while (search-forward "\t" nil t)
				   (replace-match "    " nil t))
				 (cons
				  (split-string (buffer-string) "\n")
				  (mixcode-build-tbl)))))
	(setq mixcode-source-strs (car built))
	(setq mixcode-source-tbl (cdr built))))

(defun mixcode-read-source-file ()
  (read-file-name "Source file: "
				  mixcode-source-dir
				  nil nil
				  mixcode-source-file))

(defun mixcode-load-file (fname)
  "Load a Go file to mix with."
  (interactive
   (list (mixcode-read-source-file)))
  (mixcode-build-strs fname))

(define-minor-mode
  mixcode-mode
  "Mixing Go code within Coq proof."
  :lighter " mixcode"
  (mixcode-fontify-buffer))

;; TODOs
;; 1. Representation predicate generation
;; 2. Comments above


(defun mixcode-parse-signature (s)
  (string-match "^func *\\(([^()]+)\\|\\) +\\([^()]*\\)(\\([^()]*\\))\\(.*\\)" s)
  (let ((recv (match-string 1 s))
		(func (match-string 2 s))
		(args (match-string 3 s))
		(rets (match-string 4 s)))
	(list (mixcode-parse-recv recv)
		  func
		  (mixcode-parse-args args)
		  (mixcode-parse-rets rets))))

(defun mixcode-parse-recv (s)
  (if (string-match "(\\(.*\\) +\\(.*\\))" s)
	  ;; method
	  (cons (match-string 1 s) (match-string 2 s))
	;; function
	nil))

(defun mixcode-parse-args (s)
  (let ((seps
		 (reverse (mapcar
				   (lambda (x) (split-string x " " t))
				   ;; each commas separate two vars; the regexp trims away spaces
				   (split-string s "," t "[[:space:]]*"))))
		(args)
		(type))
	(dolist (elem seps args)
	  (if (cdr elem)
		  ;; has its own type
		  (progn
		   (add-to-list 'args (cons (car elem) (nth 1 elem)))
		   (setq type (nth 1 elem)))
		;; does not have its own type; use the type of the previous variable
		(add-to-list 'args (cons (car elem) type))))))

(defun mixcode-parse-rets (s)
  (split-string s "[ ,]+" t "[()]"))

(defun mixcode-gotype-to-coqtype (type)
  (cond ((equal type "uint8")         "u8")
		((equal type "uint32")        "u32")
		((equal type "uint64")        "u64")
		((equal type "bool")          "bool")
		((equal type "string")        "string")
		((string-match "\\*.+" type)  "loc")
		((string-match "\\[].+" type) "Slice.t")
		(t                            "?type")))

(defun mixcode-type-var (var)
  (format " (%s : %s)" (car var) (mixcode-gotype-to-coqtype (cdr var))))

(defun mixcode-type-vars (vars)
  (seq-reduce (lambda (s var) (concat s (mixcode-type-var var))) vars ""))

(defun mixcode-name-rets (rets)
  (let ((names
		 (mapcar (lambda (n) (format "?v%d" n)) (number-sequence 1 (length rets)))))
	(seq-mapn #'cons names rets)))

(defun mixcode-toval-formatter (type)
  (cond ((equal type "uint8")         " #%s")
		((equal type "uint32")        " #%s")
		((equal type "uint64")        " #%s")
		((equal type "bool")          " #%s")
		;; perennial seems to miss coercion of LitString?
		((equal type "string")        " #(LitString %s)")
		((string-match "\\*.+" type)  " #%s")
		((string-match "\\[].+" type) " (to_val %s)")
		(t                            " (?to_val %s)")))

(defun mixcode-toval-var (var)
  (format (mixcode-toval-formatter (cdr var)) (car var)))

(defun mixcode-toval-vars (vars)
  (seq-reduce (lambda (s var) (concat s (mixcode-toval-var var))) vars ""))

(defun mixcode-insert-theorem (sig)
  ;; this would be ambiguous for reference/non-refererence receiver
  (let* ((p (mixcode-parse-signature sig))
		 (recv (nth 0 p))
		 (func (nth 1 p))
		 (args (nth 2 p))
		 (rets (nth 3 p))
		 (name (if recv (format "%s__%s" (string-trim (cdr recv) "\\*" nil) func) func))
		 (args-recv (if recv (cons recv args) args))
		 (typed-args (mixcode-type-vars args-recv))
		 ;; handle function without argument
		 (value-args (if args-recv (mixcode-toval-vars args-recv) " #()"))
		 (named-rets (mixcode-name-rets rets))
		 (typed-rets (if rets (format "%s," (mixcode-type-vars named-rets)) ""))
		 ;; handle function without return value
		 (value-rets (if rets (mixcode-toval-vars named-rets) " #()")))
	(insert
	 (format
	  ;; TODO: a better way is to use `indent-region', but right now the
	  ;; postcondition seems incorrectly indented, so manual indentation for now.
	  "Theorem wp_%s%s :\n  {{{ True }}}\n    %s%s\n  {{{%s RET%s; True }}}.\nProof.\n"
	  name typed-args name value-args typed-rets value-rets))))

;;; Test cases

;; (defconst f1 "func (tuple *Tuple) appendVersion(tid  uint64 , val ,  y string)")
;; (defconst f2 "func (tuple *Tuple) Free() ( A  ,  uint8 )")
;; (defconst f3 "func MkTuple() *Tuple")
;; (defconst f4 "func findVersion(tid uint64, vers []Version) Version")
;; (mixcode-parse-signature f2)

;; Generation of representation predicates based on struct definition

(defun mixcode-is-struct (key value)
  (string-match "^type .* struct" key))

(defun mixcode-insert-rp (name)
  "Insert representation predicate."
  (interactive
   (list (progn
		   (unless mixcode-source-strs (error "Run `mixcode-load-file' first."))
		   (completing-read "Struct name: "
							mixcode-source-tbl
							'mixcode-is-struct))))
  (let ((range (gethash name mixcode-source-tbl)))
	(unless range (error "Unknown struct name."))
	(let ((begin (point)))
	  (mixcode-insert-lines (number-sequence (car range) (cdr range)))
	  (mixcode-insert-rp-def (number-sequence (car range) (1- (cdr range))))
	  (indent-region begin (point)))))

(defun mixcode-parse-field (str)
  (string-match "\\([^[:blank:]]*\\)[[:blank:]]+\\([^[:blank:]]*\\)" str)
  (cons (match-string 1 str) (match-string 2 str)))

(defun mixcode-parse-struct-name (str)
  (string-match "^type[[:blank:]]+\\([^[:blank:]]+\\)[[:blank:]]+struct" str)
  (match-string 1 str))

(defun mixcode-insert-rp-header (name)
  (insert
   (format "Definition own_%s (%s : loc) : iProp Σ :=\n"
		   (downcase name) (downcase name))))

(defun mixcode-insert-rp-exists (fields)
  (insert (format "∃%s,\n" (mixcode-type-vars fields))))

(defun mixcode-insert-rp-resources (name fields)
  (while fields
	(let ((field (car fields)))
	  (insert (format
			 "\"H%s\" ∷ %s ↦[%s :: \"%s\"]%s"
			 (car field)
			 (downcase name)
			 name
			 (car field)
			 (mixcode-toval-var field))))
	(setq fields (cdr fields))
	;; insert sep and newline if there are more resources
	(when fields
	  (insert " ∗\n")))
  (insert "."))

;; TODO:
;; 1. insert known resources such as mutexes, slices, maps
;; 2. insert mu to is_struct
;; 3. annotate read-only

(defun mixcode-insert-rp-def (lines)
  ;; first line is struct names, remainings are fields
  (let* ((name (mixcode-parse-struct-name (mixcode-source-str-at (car lines))))
		 (fields (mixcode-parse-fields name (cdr lines))))
	(mixcode-insert-rp-header name)
	(mixcode-insert-rp-exists fields)
	(mixcode-insert-rp-resources name fields)
	(print name)
	(print fields)))

(defun mixcode-parse-fields (name lines)
  (let ((fields))
	(dolist (line lines fields)
	  (let ((str (string-trim (mixcode-source-str-at line))))
		;; ignore empty and comment lines
		(unless (or (equal "" str) (string-match "^\/\/.*" str))
		  (add-to-list 'fields (mixcode-parse-field str) t))))))

(defun mixcode-source-str-at (n)
  (nth (1- n) mixcode-source-strs))
