#lang racket

;Kernan Lee & Hanshuo Geng

(require "../chez-init.rkt")
(provide eval-one-exp reset-global-env)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data (lambda(exp) (or (number? exp) (null? exp) (vector? exp)(boolean? exp)(string? exp)(list? exp)(symbol? exp))))]
  [lambda-exp
   (id (lambda(params) (or(symbol? params) (list? params))))
   (body (list-of? expression?))]
  [lambda-onesym-exp
   (id symbol?)
   (body (list-of? expression?))]
  [lambda-pair-exp
   (id pair?)
   (body (list-of? expression?))]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))]
  [if-exp
   (ifcond expression?)
   (ifbody expression?)
   (elsebody expression?)]
  [onearmif-exp
   (ifcond expression?)
   (truebody expression?)]
  [cond-exp
   (bodies (list-of? expression?))
   (else expression?)]
  [noelsecond-exp
   (bodies (list-of? expression?))]
  [let-exp
   (instancevars list?)
   (body (list-of? expression?))]
  [letrec-exp
   (proc-names (list-of? symbol?))
   (idss (list-of? (list-of? symbol?)))
   (bodiess (list-of? (list-of? expression?)))
   (letrec-bodies (list-of? expression?))]
  [let*-exp
   (instancevars list?)
   (body (list-of? expression?))]
  [namedlet-exp
   (namedvar symbol?)
   (idss (list-of? symbol?))
   (bodiess (list-of? expression?))
   (namedbody (list-of? (list-of? expression?)))]
  [set!-exp
   (id symbol?)
   (body expression?)]
  [define-exp
    (id symbol?)
    (body expression?)]
  [begin-exp
   (body (list-of? expression?))]
  [or-exp
   (body (list-of? expression?))]
  [while-exp
   (ifcond expression?)
   (body (list-of? expression?))]
)

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  



; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (ids (lambda(id)(or((list-of? symbol?) id)((list-of? null?) id))))
   (bodies (list-of? expression?))
   (env environment?)]
  [closure-onesym
   (ids (list-of? symbol?))
   (bodies (list-of? expression?))
   (env environment?)]
  [closure-pair
   (ids pair?)
   (bodies (list-of? expression?))
   (env environment?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Helper procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

; Again, you'll probably want to use your code from A11b


(define parse-exp         
  (lambda (datum)
    (cond
      [(null? datum) (lit-exp datum)]
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(vector? datum) (lit-exp datum)]
      [(boolean? datum) (lit-exp datum)]
      [(string? datum) (lit-exp datum)]
      [(list? datum)
       (cond
         [(eqv? (1st datum) 'quote) (lit-exp (2nd datum))]
         [(eqv? (car datum) 'lambda)
          (cond[(< (length datum) 3) (error 'parse-exp "bad expression: ~s" datum)]
               [(symbol? (2nd datum))
                (lambda-onesym-exp (cadr datum) (map parse-exp (cddr datum)))]
               [(and(not(list? (2nd datum)))(pair? (2nd datum)))
                (lambda-pair-exp (cadr datum) (map parse-exp (cddr datum)))]
               [(not(andmap symbol? (2nd datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(null? (2nd datum))
                (lambda-exp '() (map parse-exp (cddr datum)))]
               [(list? (2nd datum))
                (lambda-exp (map parse-exp (2nd  datum))
                      (map parse-exp (cddr datum)))]
               [else (lambda-exp (map parse-exp (2nd  datum))
                      (map parse-exp (cddr datum)))])]
         [(eqv? (car datum) 'if)
          (cond[(or(< 4 (length datum))(> 3 (length datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(= 3 (length datum)) (onearmif-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
               [else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (cadddr datum)))])]
         [(eqv? (car datum) 'cond)
          (cond[#f (error 'parse-exp "bad expression: ~s" datum)]
               [(not(eqv? 'else (car(get-last datum)))) (noelsecond-exp (map parse-exp (remove-last (cdr datum))))]
               [else(cond-exp (map parse-exp (remove-last (cdr datum))) (parse-exp (cadr(get-last datum))))])]
         [(eqv? (car datum) 'let)
          (cond[(< (length datum) 3) (error 'parse-exp "bad expression: ~s" datum)]
               [(symbol? (cadr datum))
                (namedlet-exp (cadr datum) (map car (caddr datum)) (map (lambda(x)(parse-exp(cadr x))) (caddr datum)) (list(map parse-exp (cdddr datum))))]
               [(not(list? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap list? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap (lambda (x) (= 2 (length x))) (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap (lambda (x) (and (symbol? (car x)) (expression? (parse-exp (cadr x))))) (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [else (let-exp (map (lambda(x) (list (parse-exp (car x))(parse-exp (cadr x)))) (cadr datum))
                              (map parse-exp (cddr datum)))])]
         [(eqv? (car datum) 'letrec)
          (cond[(< (length datum) 3) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(list? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap list? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap (lambda (x) (= 2 (length x))) (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap (lambda (x) (and (symbol? (car x)) (expression? (parse-exp (cadr x))))) (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [else (letrec-exp (map (lambda(exp) (car exp)) (cadr datum))
                                  (map (lambda(exp) (cadr (cadr exp))) (cadr datum))
                                  (map (lambda(exp) (list(parse-exp(car(cddr(car(cdr exp)))))))(cadr datum))
                                  (map parse-exp(cddr datum)))])]
         [(eqv? (car datum) 'let*)
          (cond[(< (length datum) 3) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(list? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap list? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap (lambda (x) (= 2 (length x))) (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(andmap (lambda (x) (and (symbol? (car x)) (expression? (parse-exp(cadr x))))) (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [else (let*-exp (map (lambda(x) (list (parse-exp (car x))(parse-exp (cadr x)))) (cadr datum))
                              (map parse-exp (cddr datum)))])]
         [(eqv? (car datum) 'set!)
          (cond[(not(= 3 (length datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [(not(symbol? (cadr datum))) (error 'parse-exp "bad expression: ~s" datum)]
               [else (set!-exp (cadr datum) (parse-exp (caddr datum)))])]
         [(eqv? (car datum) 'define)
          (cond[#f 'errorcase]
               [else (define-exp (cadr datum) (parse-exp (caddr datum)))])]
         [(eqv? (car datum) 'or)
          (cond[#f 'todo]
               [else(or-exp (map parse-exp (cdr datum)))])]
         [(eqv? (car datum) 'begin)
          (cond[#f 'errortodo]
               [else (begin-exp (map parse-exp (cdr datum)))])]
         [(eqv? (car datum) 'while)
          (cond[#f 'possible-error]
               [else (while-exp (parse-exp(cadr datum))(map parse-exp (cddr datum)))])]
         [else(app-exp (parse-exp (1st datum))
		      (map parse-exp (cdr datum)))])]
         [else (error 'parse-exp "bad expression: ~s" datum)])))






(define get-last
  (lambda (exp)
    (cond [(null? (cdr exp)) (car exp)]
          [else
           (get-last (cdr exp))])))

(define remove-last
  (lambda (exp)
    (cond [(null? (cdr exp))'()]
          [else (cons (car exp) (remove-last (cdr exp)))])))

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

;Creating cells for set!

(define cell
  (lambda (val)
    (box val)))
(define cell-ref unbox)
(define cell-set! set-box!)
(define cell?
  (lambda (obj)
    (box? obj)))
(define deref cell-ref)
(define set-ref! cell-set!)




;Environments
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)]
  [recursively-extended-env-record
   (proc-names (list-of? symbol?))
   (idss (list-of? (list-of? symbol?)))
   (bodiess (list-of? (list-of? expression?)))
   (old-env environment?)])

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map cell vals) env)))

(define extend-env-recursively
  (lambda(pn idss bodiess old-env)
    (recursively-extended-env-record pn idss bodiess old-env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))

(define apply-env
  (lambda(env var)
    (deref (apply-env-ref env var))))

(define apply-env-ref
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (apply-global-env sym global-env)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env-ref env sym)))]
      [recursively-extended-env-record(pn idss bodiess old-env)
                                      (let ((pos (list-find-position sym pn)))
                                        (if(number? pos)
                                           (cell (closure (list-ref idss pos)
                                                          (list-ref bodiess pos)
                                                          env))
                                           (apply-env-ref old-env sym)))])))


(define apply-global-env
  (lambda (sym env)
    (cases environment env
      [extended-env-record (syms vals env)
                           (let ([pos (list-find-position sym syms)])
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-global-env sym env)))]
      [empty-env-record ()
                        (error 'global-env "This should never happen")]
      [else sym])))

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [cond-exp (body else)
                (cond[(null? body) (syntax-expand else)]
                     [else (if-exp (syntax-expand (cadar body)) (syntax-expand (car(caddar body))) (syntax-expand (cond-exp (cdr body) else)))])]
      [noelsecond-exp(body)
                     (cond[(null? (cdr body)) (onearmif-exp (cadar body) (car(caddar body)))]
                          [else (if-exp (syntax-expand (cadar body)) (syntax-expand (car(caddar body))) (syntax-expand (noelsecond-exp (cdr body))))])]
;      [or-exp(bodies)
 ;            (cond[(null? bodies) (parse-exp #f)]
  ;                [else (if-exp (syntax-expand (car bodies)) (syntax-expand(car bodies)) (syntax-expand (or-exp (cdr bodies))))])]
      [or-exp(bodies)
             (cond[(null? bodies) (parse-exp #f)]
                  [else (syntax-expand(let-exp (list(list(var-exp 'x) (1st bodies))) (list(if-exp (var-exp 'x)(var-exp 'x)(or-exp (cdr bodies))))))])]
      [begin-exp (exps) (app-exp (lambda-exp (list) (map syntax-expand exps)) (list))]
      [let-exp(instancevars bodies)
              (app-exp (lambda-exp (map car instancevars) (map syntax-expand bodies)) (map syntax-expand (map 2nd instancevars)))]
      [let*-exp(instancevars body)(cond[(null? (cdr instancevars)) (syntax-expand(let-exp (list(list (caar instancevars)(cadr(car instancevars)))) body))]
                                       [else(syntax-expand(let-exp (list(list (caar instancevars)(cadr(car instancevars)))) (list(let*-exp(cdr instancevars)body))))])]
      [namedlet-exp (names idss bodies namedlet-bodies)
        (syntax-expand(letrec-exp (list names) (list idss) (map (lambda(x) (map syntax-expand x)) namedlet-bodies) (list (app-exp (var-exp names) (map syntax-expand bodies)))))]
      [if-exp(ifcond ifbody elsebody)
             (if-exp (syntax-expand ifcond)(syntax-expand ifbody)(syntax-expand elsebody))]
      [onearmif-exp(ifcond truebody)
                  (onearmif-exp (syntax-expand ifcond)(syntax-expand truebody))]
      [lambda-exp (id body)
                  (lambda-exp id (map syntax-expand body))]
      [letrec-exp(np idss bodiess lrbodies)
                 (letrec-exp np idss (map (lambda(x) (map syntax-expand x)) bodiess) (map syntax-expand lrbodies))]
      [app-exp (rator rands)
               (app-exp (syntax-expand rator) (map syntax-expand rands))]
      [while-exp (ifcond body)
                 (while-exp (syntax-expand ifcond) (map syntax-expand body))]
      [define-exp (id body)
        (define-exp id (syntax-expand body))]
      [else exp])))

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form (empty-env))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp rator env)]
                     [args (eval-rands rands env)])
                 (apply-proc proc-value args))]
      [if-exp (ifcond ifbody elsebody)
              (if(eval-exp ifcond env)
                 (eval-exp ifbody env)
                 (eval-exp elsebody env))]
      [onearmif-exp (ifcond truebody)
                    (if(eval-exp ifcond env)
                       (eval-exp truebody env)
                       (void))]
      [let-exp (instancevars body)(eval-one-exp '(begin (define a 5) (+ a 3)))
               (let ((names (map (lambda(x) (cadr(car x))) instancevars))
                     (init-exps (map (lambda (y) (cadr y)) instancevars)))
                 (eval-bodies body (extend-env names (eval-rands init-exps env) env)))]
      [letrec-exp(proc-names idss bodies letrec-bodies)
                 (eval-bodies letrec-bodies
                              (extend-env-recursively proc-names idss bodies env))]
      [while-exp (prec body) (when (eval-exp prec env)
                             (begin (eval-bodies body env)(eval-exp (while-exp prec body) env)))]
      [set!-exp (id body)
                (set-ref!
                 (apply-env-ref env id)
                 (eval-exp body env))]
                ;(set! id body)]
      [define-exp (id body)
        (let ([old-global-env global-env])
          (begin (set! global-env (extend-env (list id)(list(eval-exp body old-global-env)) old-global-env))))]
      [lambda-exp (ids bodies)
                  (closure (map cadr ids) bodies env)]
      [lambda-onesym-exp (id bodies)
                         (closure-onesym (list id) bodies env)]
      [lambda-pair-exp(ids bodies)
                      (closure-pair ids bodies env)]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define eval-bodies
  (lambda (bodies env)
    (if (null? (cdr bodies))
        (eval-exp (car bodies) env)
        (begin
          (eval-exp (1st bodies) env)
          (eval-bodies (cdr bodies) env)))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (e) (eval-exp e env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [closure (ids bodies env) (eval-bodies bodies (extend-env ids args env))]
      [closure-onesym (id bodies env) (eval-bodies bodies (extend-env id (list args) env))]
      [closure-pair (ids bodies env) (let ([mdfarg (letrec ([mdf (lambda (p ls)
                                      (if (symbol?(cdr p)) (list (list (car p) (cdr p)) (list (car ls) (cdr ls))) (let ([rs (mdf (cdr p) (cdr ls))])
                                      (list (cons (car p) (car rs)) (cons (car ls) (cadr rs))))))])
                     (mdf ids args))]) (eval-bodies bodies (extend-env (1st mdfarg) (2nd mdfarg) env)))]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons = quote / not zero? >= car cdr list null? eq? equal? length vector->list list->vector list? pair? vector? number? symbol? caar cadr cadar procedure?
                              vector-set! vector-ref vector map apply > < quotient negative? positive? list-tail eqv? append))



; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (/ (car args) (cadr args))]
      [(quotient) (quotient (car args)(cadr args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(list-tail) (list-tail (car args)(cadr args))]
      [(=) (= (1st args) (2nd args))]
      [(not) (not (car args))]
      [(zero?) (zero? (car args))]
      [(eqv?)(eqv? (car args)(cadr args))]
      [(>=) (>= (car args)(cadr args))]
      [(<=) (<= (car args) (cadr args))]
      [(<) (< (car args) (cadr args))]
      [(>) (> (car args) (cadr args))]
      [(car) (caar args)]
      [(positive?)(positive? (car args))]
      [(negative?)(negative? (car args))]
      [(pair?)(pair? (car args))]
      [(vector)(apply vector args)]
      [(vector?)(vector? (car args))]
      [(vector-set!) (vector-set! (car args) (cadr args) (caddr args))]
      [(vector-ref) (vector-ref (car args) (cadr args))]
      [(procedure?)(apply proc-val? args)]
      [(cdr) (cdr(car args))]
      [(list) (apply list args)]
      [(null?)(null? (car args))]
      [(eq?) (eq? (car args)(cadr args))]
      [(list?) (list? (car args))]
      [(equal?) (equal? (car args)(cadr args))]
      [(length) (length (car args))]
      [(list->vector)(list->vector (car args))]
      [(vector->list)(vector->list (car args))]
      [(number?) (number? (car args))]
      [(symbol?) (symbol? (car args))]
      [(caar) (caar (car args))]
      [(cadar) (cadar (car args))]
      [(cadr) (cadr (car args))]
      [(map) (apply map (lambda (x) (apply-proc (car args) (list x))) (cdr args))]
      [(apply) (apply apply-proc args)]
      [(append) (apply append args)]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.



(define make-init-env         ; for now, our initial global environment only contains 
  (lambda()
    (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env))))

(define init-env
  (make-init-env))

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))

(define global-env init-env)

(define reset-global-env
 (lambda () (set! global-env (make-init-env))))
