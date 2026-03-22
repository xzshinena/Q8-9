;; collab w/ Parmida Wang
#lang racket

(provide primplify)

(define (nat? n) (and (integer? n) (>= n 0)))

;; primplify : (listof A-PRIMPL stmt) -> (listof PRIMPL stmt-or-value)
(define (primplify aprimpl)
  ;; type is 'label, 'const, 'data, or 'const-resolving (temporary)
  (define sym-table (make-hash))

  (define data-entries '())

  (define code-size 0)
  ;; code-size is how many list items will be output by the final list
  ;; for example lable produces 0 and print produces 1
  ;; all instructions produce 1 except label, data,const

  ;; this for loop is the initial parse that updates code-size + label const data
  (for ([inst aprimpl])
    (match inst
      [(list 'label sym) (when (hash-has-key? sym-table sym)
                           (error 'primplify "duplicate"))
                         (hash-set! sym-table sym (list 'label code-size))]
      
      [(list 'const sym val) (when (hash-has-key? sym-table sym)
                               (error 'primplify "duplicate"))
                             (hash-set! sym-table sym (list 'const val))]
      
      [(list 'data sym vals ...) (when (hash-has-key? sym-table sym)
                                   (error 'primplify "duplicate"))
                                 (hash-set! sym-table sym (list 'data #f)) ;; save in symbol table
                                 (set! data-entries (cons (cons sym vals) data-entries))] ;; save in data table
      
      [(list 'halt) (set! code-size (add1 code-size))]
      
      [_ (set! code-size (add1 code-size))])) ;; bc everything else is just 1

  ;; reverse bc we cons-ed on the front
  (set! data-entries (reverse data-entries))

  ;; add mem addresses to each instruction
  (let ([addr code-size])
    (for ([entry data-entries])
      (define sym (car entry))
      (define vals (cdr entry)) ;; since there can be more than 1
      (hash-set! sym-table sym (list 'data addr))

      ;; determins how many list slots data will take bc
      ;; (data name 5 10) -> 2 slots
      ;; (data name (5 10)) -> 5 slots
      (define n-slots
        (match vals
          [(list (list (? nat? n) _)) n]
          [_ (length vals)]))
      (set! addr (+ addr n-slots))))

  ;; resolve : (listof (list (union const const-resolving label data) psymbol-or-value)) -> (listof (list (union const const-resolving label data) value))
  ;; resolves const by chasing psymbol-or-value until hit a nat
  ;; if hit const we alr saw => circular => error
  (define (resolve sym)
    (match (hash-ref sym-table sym #f)
      
      [#f (error 'primplify "undefined")]
      
      [(list 'const-resolving) (error 'primplify "circular")]
      
      [(list 'const (? symbol? next))
       (hash-set! sym-table sym (list 'const-resolving))
       (define v (resolve next))
       (hash-set! sym-table sym (list 'const v))
       v]
      
      [(list 'const v) v]
      
      [(list 'label addr) addr]
      
      [(list 'data addr) addr]
      ))

  ;; this loop iterates hashtable and collects only 'const types
  (define const-syms
    (for/list ([(sym entry) (in-hash sym-table)]
               #:when (eq? (first entry) 'const))
      sym))

  ;; then call (resolve ...) on each item in teh hash table to resolve circular
  (for-each resolve const-syms)


  ;; sym-val : (list type val) -> val
  (define (sym-val s)
    (second (hash-ref sym-table s
                      (lambda () (error 'primplify "undefined")))))

  ;; sym-type : (list type val) -> type
  (define (sym-type s)
    (first (hash-ref sym-table s
                     (lambda () (error 'primplify "undefined")))))

  ;; td : A-PRIMPL-psymbol-or-value -> PRIMPL-dest
  ;; translate dest position
  (define (td d)
    (cond
      [(symbol? d)
       (case (sym-type d)
         [(data) (list (sym-val d))]
         [else (error 'primplify "incorrect")])]
      [(and (list? d) (= (length d) 2))
       (list (ti (first d)) (tn (second d)))]
      [else d]))

  ;; next 5 fxns (to, tt, ti, tn, tv) are helpers to convert A-PRIMPL pysmbol-or-value to PRIMPL value/opd/dest/imm/ind

  ;; to : A-PRIMPL-psymbol-or-value -> PRIMPL-opd
  ;; translate operand position
  ;; data->(addr), const->val, label->error
  (define (to o)
    (cond
      [(symbol? o)
       (case (sym-type o)
         [(data) (list (sym-val o))]
         [(const) (sym-val o)]
         [(label) (error 'primplify "incorrect")])]
      [(and (list? o) (= (length o) 2))
       (list (ti (first o)) (tn (second o)))]
      [else o]))

  ;; tt : A-PRIMPL-psymbol-or-value -> PRIMPL-(union imm ind)
  ;; translate jump/branch target
  ;; label->addr(imm), data->(addr), const->(val)
  (define (tt o)
    (cond
      [(symbol? o)
       (case (sym-type o)
         [(label) (sym-val o)]
         [(data) (list (sym-val o))]
         [(const) (list (sym-val o))])]
      [(and (list? o) (= (length o) 2))
       (list (ti (first o)) (tn (second o)))]
      [else o]))

  ;; ti : A-PRIMPL-psymbol-or-ind -> PRIMPL-value
  ;; translate imm
  ;; any symbol -> immediate value
  (define (ti a)
    (if (symbol? a) (sym-val a) a))

  ;; tn : A-PRIMPL-psymbol -> PRIMPL-ind
  ;; translate ind
  ;; data->(addr), else->error
  (define (tn b)
    (cond
      [(symbol? b)
       (case (sym-type b)
         [(data) (list (sym-val b))]
         [else (error 'primplify "incorrect")])]
      [else b]))

  ;; tv : A-PRIMPL-psymbol-or-value -> PRIMPL-value
  ;; translate value
  ;; any symbol -> immediate value
  (define (tv v)
    (if (symbol? v) (sym-val v) v))

  ;; build the list of PRIMPL instructions using translation helpers
  (define code
    (reverse
     (for/fold ([acc empty]) ([inst aprimpl])
       (match inst
         [(list 'label _) acc]
         [(list 'const _ _) acc]
         [(list 'data _ _ ...) acc]
         [(list 'halt) (cons 0 acc)]
         [(list 'jump target)
          (cons (list 'jump (tt target)) acc)]
         [(list 'branch cnd target)
          (cons (list 'branch (to cnd) (tt target)) acc)]
         [(list 'print-val op)
          (cons (list 'print-val (to op)) acc)]
         [(list 'print-string s)
          (cons (list 'print-string s) acc)]
         [(list 'lnot dest op)
          (cons (list 'lnot (td dest) (to op)) acc)]
         [(list 'move dest op)
          (cons (list 'move (td dest) (to op)) acc)]
         [(list op dest op1 op2)
          (cons (list op (td dest) (to op1) (to op2)) acc)]))))

  ;; append data vals at end of instruction list
  (define data-vals
    (apply append
     (for/list ([entry data-entries])
       (define vals (cdr entry))
       (match vals
         [(list (list (? nat? n) val))
          (make-list n (tv val))]
         [_ (map tv vals)]))))
  (append code data-vals))


