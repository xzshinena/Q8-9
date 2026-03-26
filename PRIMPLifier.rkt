#lang racket

(define (primplify prog-list)
  (define sym-table (make-hash))
  (define counter 0)
  (define result empty)
  (first-pass prog-list sym-table counter)
  (resolve sym-table)  ;; mutated hash table will then be resolved here
  (second-pass prog-list sym-table result))

;; all this does is mutate the hash table
(define (first-pass prog-list sym-table counter)
  (cond
    [(empty? prog-list) (void)]
    [else
     (define inst (first prog-list))
     (define new-counter
       (match inst
         [`(const ,name ,val) (if (hash-has-key? sym-table name)
                                  (error 'primplify "duplicate")
                                  (hash-set! sym-table name (list 'const val)))
                              counter]
         [`(data ,name ,val ...) (if (hash-has-key? sym-table name)
                                     (error 'primplify "duplicate")
                                     (hash-set! sym-table name (list 'data counter)))
                                 (if (list? (first val)) ;; handles statements of the form (data sym (nat sym-or-val))
                                     (+ counter (first (first val)))
                                     (+ counter (length val)))]
         [`(label ,name) (if (hash-has-key? sym-table name)
                             (error 'duplicate)
                             (hash-set! sym-table name (list 'label counter)))
                         counter]
         [_ (add1 counter)]))
     (first-pass (rest prog-list) sym-table new-counter)]))

(define (resolve sym-table)
  (for ([(key value) (in-hash sym-table)])
    (hash-set! sym-table key (find-val sym-table key))))

(define (find-val sym-table key (existing (set))) ;; default value of existing is the empty set
  (when (set-member? existing key) ;; use 'when' instead of 'if' because 'if' requires you to specify an else case
    (error 'primplify "circular")) 
  (define val (hash-ref sym-table key #f))
  (cond
    [(not val) (error 'primplify "undefined")]
    [else
     (match val
       [`(const ,(? symbol? s))
         (define resolved (find-val sym-table s (set-add existing key)))
         (list 'const (if (list? resolved) (second resolved) resolved))]
       [`(data ,(? symbol? s))
         (define resolved (find-val sym-table s (set-add existing key)))
         (list 'data (if (list? resolved) (second resolved) resolved))]
       [_ val])]))

(define (second-pass prog-list sym-table result)
  (cond
    [(empty? prog-list) (reverse result)]
    [else
     (define inst (first prog-list))
     (define inst-result (convert sym-table inst))
     (second-pass (rest prog-list) sym-table (foldl cons result inst-result))]))

;; wrap each result in a list to ensure compatability with foldl
(define (convert sym-table inst)
  (match inst
    [`(const ,name ,val) empty]
    [`(data ,name ,val ...) (if (list? (first val))
                                (for/list ([i (range (first (first val)))]) (convert-opd sym-table (second (first val)) #t))
                                (map (lambda (v) (convert-opd sym-table v #t)) val))]
    [`(label ,name) empty]
    [`(,op ,dest ,opd1 ,opd2) (list (list op (convert-dest sym-table dest)
                                             (convert-opd sym-table opd1)
                                             (convert-opd sym-table opd2)))]
    [`(lnot ,dest ,opd) (list (list 'lnot (convert-dest sym-table dest)
                                          (convert-opd sym-table opd)))]
    [`(jump ,opd) (list (list 'jump (convert-opd sym-table opd #f #t)))]
    [`(branch ,opd1 ,opd2) (list (list 'branch (convert-opd sym-table opd1 #f #f)
                                               (convert-opd sym-table opd2 #f #t)))]
    [`(move ,dest ,opd) (list (list 'move (convert-dest sym-table dest)
                                          (convert-opd sym-table opd)))]
    [`(print-val ,opd) (list (list 'print-val (convert-opd sym-table opd)))]
    [`(print-string ,str) (list (list 'print-string str))]
    [`(halt) (list 0)]
    [(? integer? v) (list v)]
    [(? boolean? v) (list v)]
    [(? symbol? v) (define val (hash-ref sym-table v #f))
                   (if val (list (second val)) (error 'primplify "undefined"))]))

;; include optional data-as-imm? param to account for the case where a psymbol defined in a data statement
;; is used as an immediate operand in another data statement
(define (convert-opd sym-table opd (data-as-imm? #f) (label-ok? #f))
  (cond
    [(symbol? opd)
     (define resolved (hash-ref sym-table opd #f))
     (when (not resolved) (error 'primplify "undefined symbol ~a" opd))
     (match resolved
       [`(const ,n) n]
       [`(data ,n) (if data-as-imm? n (list n))]
       [`(label ,n) (if (or label-ok? data-as-imm?) n (error 'primplify "incorrect use of label: ~a" opd))])]
    [(and (list? opd) (= (length opd) 2) (symbol? (first opd)))
     ;; indexed case like (A (5)) where A is a data psymbol used as immediate
     (define resolved (hash-ref sym-table (first opd)))
     (match resolved
       [`(data ,n) (list n (second opd))]
       [`(const ,n) (list n (second opd))]
       [_ (error 'primplify "incorrect psymbol in indexed position")])]
    ;; list operand contains symbol
    [(and (list? opd) (= (length opd) 1) (symbol? (first opd)))
     (define resolved (hash-ref sym-table (first opd)))
     (match resolved
       [`(data ,n) (list n)]
       [_ (error 'primplify "incorrect psymbol in indirect position")])]
    [else opd]))

(define (convert-dest sym-table dest)
  (cond
    [(symbol? dest)
     (define resolved (hash-ref sym-table dest))
     (match resolved
       [`(data ,n) (list n)]
       [_ (error 'primplify "incorrect")])] ;; handles case where const occurs as a dest
    [(and (list? dest) (= (length dest) 1) (symbol? (first dest)))
     (define resolved (hash-ref sym-table (first dest)))
     (match resolved
       [`(data ,n) (list n)]
       [_ (error 'primplify "incorrect psymbol in indirect dest position")])]
    [else dest]))

;; (data X 1)
;; (data Y X)

;; (const A B)
;; (const B 10)
;; (add Y Y A)
;; (data Y 20 B)
;; produces '((add (1) (1) 10)
;;            20
;;            10)

;; (const A B)
;; (const B 10)
;; (add Y Y A)
;; (data Y 20)
;; produces '((add (1) (1) 10)
;;            20)

;; (const A B)
;; (const B 10)
;; (add Y Y A)
;; (data Y 20)
;; produces '(20
;;            (add (0) (0) 10))

;; when you see a const instruction don't increment the counter
