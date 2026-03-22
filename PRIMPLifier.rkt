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
                                (error 'duplicate)
                                (hash-set! sym-table name (list 'const val)))
                              counter]
         [`(data ,name ,val) (if (hash-has-key? sym-table name)
                               (error 'duplicate)
                               (hash-set! sym-table name (list 'data counter)))
                             (add1 counter)]
         [_ (add1 counter)]))
     (first-pass (rest prog-list) sym-table new-counter)]))

(define (resolve sym-table)
  (for ([(key value) (in-hash sym-table)])
    (hash-set! sym-table key (find-val sym-table key))))

(define (find-val sym-table key (visiting (set))) ;; default value of visiting is the empty set
  (when (set-member? visiting key) ;; use 'when' instead of 'if' because 'if' requires you to specify an else case
    (error 'circular)) 
  (define val (hash-ref sym-table key #f))
  (cond
    [(not val) (error 'undefined)]
    [else
     (match val
       [`(const ,(? symbol? s))
         (define resolved (find-val sym-table s (set-add visiting key)))
         (list 'const (if (list? resolved) (second resolved) resolved))]
       [`(data ,(? symbol? s))
         (define resolved (find-val sym-table s (set-add visiting key)))
         (list 'data (if (list? resolved) (second resolved) resolved))]
       [_ val])]))

(define (second-pass prog-list sym-table result)
  (cond
    [(empty? prog-list) (reverse result)]
    [else
     (define inst (first prog-list))
     (define inst-result (convert sym-table inst))
     (second-pass (rest prog-list) sym-table (if (empty? inst-result)
                                                 result
                                                 (cons inst-result result)))]))

(define (convert sym-table inst)
  (match inst
    [`(const ,name ,val) empty]
    [`(data ,name ,val) val]
    [`(add ,dest ,opd1 ,opd2) (list 'add (convert-dest sym-table dest)
                                         (convert-opd sym-table opd1)
                                         (convert-opd sym-table opd2))]
    [`(halt) 0]))

(define (convert-opd sym-table opd)
  (cond
    [(symbol? opd)
     (define resolved (hash-ref sym-table opd))
     (match resolved
       [`(const ,n) n]
       [`(data ,n) (list n)])]
    [(list? opd) opd]
    [else opd]))

(define (convert-dest sym-table dest)
  (cond
    [(symbol? dest)
     (define resolved (hash-ref sym-table dest))
     (match resolved
       [`(data ,n) (list n)]
       [_ (error 'bad)])]
    [(list? dest) dest]
    [else dest]))

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