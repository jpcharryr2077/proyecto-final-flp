#lang eopl

;******************************************************************************************
; Proyecto final de curso - Flowlang
; Integrantes:
; [Juan Felipe Palechor 2270963]
; [Juan Esteban Rodriguez 2042282]
; [Juan Pablo Charry 2040579]
; Curso: Fundamentos de Lenguajes de Programación
; Profesor: Robinson Duque
; URL del repositorio: https://github.com/jpcharryr2077/proyecto-final-flp.git
;******************************************************************************************

; =============================================
; Commit 3: FlowLang - AMBIENTE CORREGIDO (con fixes)
; =============================================

; Scanner 
(define scanner-spec-flowlang
  '((white-sp (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit) "." digit (arbno digit)) number)
    (number ("-" digit (arbno digit) "." digit (arbno digit)) number)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (string (#\" (arbno (not #\")) #\") string)
    (boolean ("true") symbol)
    (boolean ("false") symbol)))

; Gramática 
(define grammar-flowlang
  '((program (expression) un-programa)

    ; Expresiones básicas
    (expression (number)   const-num-exp)
    (expression (string)   const-str-exp)
    (expression (boolean)  const-bool-exp)
    (expression ("null")   const-null-exp)

    ; Variables y asignación 
    (expression ("var" identifier "=" expression) var-decl-exp)
    (expression ("set" identifier "=" expression) assign-exp)

    ; Funciones 
    (expression ("func" "(" (separated-list identifier ",") ")" "{" expression "}") func-exp)

    ; IDENT o APLICACIÓN 
    (expression (identifier (arbno "(" (separated-list expression ",") ")")) app-or-var-exp)

    ; Operaciones binarias 
    (expression ("(" expression primitive-bin expression ")") primapp-bin-exp)

    ; Operaciones unarias
    (expression (primitive-unaria "(" expression ")") primapp-un-exp)

    ; Control de flujo
    (expression ("if" expression "then" expression "else" expression "end") if-exp)
    (expression ("begin" (separated-list expression ";") "end") begin-exp)

    ; Primitivas binarias
    (primitive-bin ("+")      primitiva-suma)
    (primitive-bin ("-")      primitiva-resta)
    (primitive-bin ("*")      primitiva-multi)
    (primitive-bin ("/")      primitiva-div)
    (primitive-bin ("concat") primitiva-concat)
    (primitive-bin ("and")    primitiva-and)
    (primitive-bin ("or")     primitiva-or)

    ; Primitivas unarias
    (primitive-unaria ("longitud") primitiva-longitud)
    (primitive-unaria ("add1")     primitiva-add1)
    (primitive-unaria ("sub1")     primitiva-sub1)
    (primitive-unaria ("not")      primitiva-not)))

; Generar datatypes
(sllgen:make-define-datatypes scanner-spec-flowlang grammar-flowlang)

; Parser
(define scan&parse-flowlang
  (sllgen:make-string-parser scanner-spec-flowlang grammar-flowlang))

; =============================================
; Tipos de valores y ambiente
; =============================================

(define-datatype expval expval?
  (num-val  (value number?))
  (bool-val (value boolean?))
  (str-val  (value string?))
  (null-val)
  (proc-val (value procval?))
  (list-val (value list?))  
  (dict-val (value list?))) 

(define-datatype procval procval?
  (closure
   (ids  (list-of symbol?))
   (body expression?)
   (env  environment?)))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?)) 
   (env  environment?))
  (recursively-extended-env-record
   (proc-names (list-of symbol?))
   (idss       (list-of (list-of symbol?))
   )
   (bodies     (list-of expression?))
   (env        environment?)))

(define scheme-value? (lambda (v) #t))

(define empty-env  (lambda () (empty-env-record)))
(define extend-env (lambda (syms vals env)
                     (extended-env-record syms vals env)))
(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (recursively-extended-env-record proc-names idss bodies old-env)))

; Búsqueda en ambiente 
(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
        (eopl:error 'apply-env "No binding for ~s" sym))
      (extended-env-record (syms vals old-env)
        (let ((pos (list-find-position sym syms)))
          (if (number? pos)
              (list-ref vals pos)
              (apply-env old-env sym))))
      (recursively-extended-env-record (proc-names idss bodies old-env)
        (let ((pos (list-find-position sym proc-names)))
          (if (number? pos)
              (closure (list-ref idss pos) (list-ref bodies pos) env)
              (apply-env old-env sym)))))))

; Auxiliares de ambiente
(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((r (list-index pred (cdr ls))))
              (if (number? r) (+ r 1) #f))))))

; =============================================
; Store para mutabilidad
; =============================================

(define the-store 'uninitialized)
(define empty-store (lambda () '()))
(define initialize-store! (lambda () (set! the-store (empty-store))))

(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec ((go (lambda (st i)
                         (cond
                           ((null? st)
                            (eopl:error 'setref "Invalid reference ~s" i))
                           ((zero? i) (cons val (cdr st)))
                           (else (cons (car st) (go (cdr st) (- i 1))))))))
            (go the-store ref)))))

; Predicado de referencia
(define reference? (lambda (v) (integer? v)))

; =============================================
; Evaluador 
; =============================================

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      ; Constantes
      (const-num-exp  (datum) (cons (num-val datum) env))
      (const-str-exp  (texto) (cons (str-val texto) env))
      (const-bool-exp (bool)  (cons (bool-val (eq? bool 'true)) env))
      (const-null-exp ()      (cons (null-val) env))

      ; Var o Aplicación 
     (app-or-var-exp (rator rands-nested)
  (if (null? rands-nested)
      (let ([binding (apply-env env rator)])
        (if (reference? binding)
            (cons (deref binding) env)    
            (cons binding env)))          
      (let* ([proc-env (eval-expression (app-or-var-exp rator '()) env)]
             [p        (car proc-env)]
             [cur-env  (cdr proc-env)])
        (let loop ([val p] [calls rands-nested] [e cur-env])
          (if (null? calls)
              (cons val e) 
              (cases expval val
                (proc-val (closure-val)
                  (let* ([args   (eval-rands (car calls) e)]
                         [result (apply-procedure closure-val args)])
                    (loop result (cdr calls) e)))
                (else (eopl:error 'app-or-var-exp "Not a procedure: ~s" val)))))))
)


      ; Declaración 
      (var-decl-exp (id val-exp)
        (let* ([ve   (eval-expression val-exp env)]
               [val  (car ve)]
               [e1   (cdr ve)]
               [ref  (newref val)])
          (cons val (extend-env (list id) (list ref) e1))))

      ; Asignación 
      (assign-exp (id val-exp)
        (let* ([ve   (eval-expression val-exp env)]
               [val  (car ve)]
               [e1   (cdr ve)]
               [ref  (apply-env e1 id)])
          (if (reference? ref)
              (begin (setref! ref val)
                     (cons val e1))
              (eopl:error 'assign-exp
                          "Variable not mutable or not a reference: ~s (got ~s)" id ref))))

      ; If
      (if-exp (test-exp true-exp false-exp)
        (let* ([te (eval-expression test-exp env)]
               [tv (car te)]
               [e1 (cdr te)])
          (if (valor-verdad? tv)
              (eval-expression true-exp e1)
              (eval-expression false-exp e1))))

      ; Begin secuencial
      (begin-exp (exps)
        (if (null? exps)
            (cons (null-val) env)
            (let loop ([xs exps] [e env] [last (null-val)])
              (if (null? xs)
                  (cons last e)
                  (let* ([re (eval-expression (car xs) e)]
                         [rv (car re)]
                         [e2 (cdr re)])
                    (loop (cdr xs) e2 rv))))))

      ; Funciones 
      (func-exp (ids body)
        (cons (proc-val (closure ids body env)) env))

      ; Binarias
      (primapp-bin-exp (exp1 prim exp2)
        (let* ([e1  (eval-expression exp1 env)]
               [v1  (car e1)]
               [env1 (cdr e1)]
               [e2  (eval-expression exp2 env1)]
               [v2  (car e2)]
               [env2 (cdr e2)])
          (cons (apply-prim-binaria prim v1 v2) env2)))

      ; Unarias
      (primapp-un-exp (prim exp1)
        (let* ([e1 (eval-expression exp1 env)]
               [v1 (car e1)]
               [e2 (cdr e1)])
          (cons (apply-primitiva-unaria prim v1) e2)))

      (else (eopl:error 'eval-expression "Expression not implemented: ~s" exp)))))

; Evalúa lista de argumentos EN SECUENCIA (izq→der)
(define eval-rands
  (lambda (rands env)
    (let loop ([es rands] [e env] [acc '()])
      (if (null? es)
          (reverse acc)
          (let* ([res (eval-expression (car es) e)]
                 [v   (car res)]
                 [e2  (cdr res)])
            (loop (cdr es) e2 (cons v acc)))))))

; Aplicar procedimiento 
(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (closure (ids body env)
        (let* ([res (eval-expression body (extend-env ids args env))])
          (car res))))))

; =============================================
; Primitivas
; =============================================

(define apply-prim-binaria
  (lambda (prim val1 val2)
    (cases primitive-bin prim
      (primitiva-suma  ()
        (if (and (num-val? val1) (num-val? val2))
            (num-val (+ (expval->num val1) (expval->num val2)))
            (eopl:error 'apply-prim-binaria "suma: se requieren números ~s ~s" val1 val2)))
      (primitiva-resta ()
        (if (and (num-val? val1) (num-val? val2))
            (num-val (- (expval->num val1) (expval->num val2)))
            (eopl:error 'apply-prim-binaria "resta: se requieren números ~s ~s" val1 val2)))
      (primitiva-multi ()
        (if (and (num-val? val1) (num-val? val2))
            (num-val (* (expval->num val1) (expval->num val2)))
            (eopl:error 'apply-prim-binaria "multi: se requieren números ~s ~s" val1 val2)))
      (primitiva-div   ()
        (if (and (num-val? val1) (num-val? val2))
            (let ([d (expval->num val2)])
              (if (zero? d)
                  (eopl:error 'apply-prim-binaria "división por cero")
                  (num-val (/ (expval->num val1) d))))
            (eopl:error 'apply-prim-binaria "div: se requieren números ~s ~s" val1 val2)))
      (primitiva-concat ()
        (if (and (str-val? val1) (str-val? val2))
            (str-val (string-append (expval->str val1) (expval->str val2)))
            (eopl:error 'apply-prim-binaria "concat: se requieren strings ~s ~s" val1 val2)))
      (primitiva-and ()
        (if (and (bool-val? val1) (bool-val? val2))
            (bool-val (and (expval->bool val1) (expval->bool val2)))
            (eopl:error 'apply-prim-binaria "and: se requieren booleanos ~s ~s" val1 val2)))
      (primitiva-or  ()
        (if (and (bool-val? val1) (bool-val? val2))
            (bool-val (or (expval->bool val1) (expval->bool val2)))
            (eopl:error 'apply-prim-binaria "or: se requieren booleanos ~s ~s" val1 val2))))))

(define apply-primitiva-unaria
  (lambda (prim val)
    (cases primitive-unaria prim
      (primitiva-longitud ()
        (if (str-val? val)
            (num-val (string-length (expval->str val)))
            (eopl:error 'apply-primitiva-unaria "longitud: se esperaba string ~s" val)))
      (primitiva-add1 ()
        (if (num-val? val)
            (num-val (+ (expval->num val) 1))
            (eopl:error 'apply-primitiva-unaria "add1: se esperaba número ~s" val)))
      (primitiva-sub1 ()
        (if (num-val? val)
            (num-val (- (expval->num val) 1))
            (eopl:error 'apply-primitiva-unaria "sub1: se esperaba número ~s" val)))
      (primitiva-not ()
        (if (bool-val? val)
            (bool-val (not (expval->bool val)))
            (eopl:error 'apply-primitiva-unaria "not: se esperaba booleano ~s" val))))))

; =============================================
; Extractores y predicados de expval
; =============================================

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (n) n)
      (else (eopl:error 'expval->num "No es un número: ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (b) b)
      (else (eopl:error 'expval->bool "No es un booleano: ~s" val)))))

(define expval->str
  (lambda (val)
    (cases expval val
      (str-val (s) s)
      (else (eopl:error 'expval->str "No es un string: ~s" val)))))

(define num-val?  (lambda (v) (cases expval v (num-val  (n) #t) (else #f))))
(define bool-val? (lambda (v) (cases expval v (bool-val (b) #t) (else #f))))
(define str-val?  (lambda (v) (cases expval v (str-val  (s) #t) (else #f))))

; Valor de verdad 
(define valor-verdad?
  (lambda (val)
    (cases expval val
      (bool-val (b) b)
      (num-val  (n) (not (zero? n)))
      (null-val ()  #f)
      (str-val  (s) (not (string=? s "")))
      (else #t))))

; =============================================
; Intérprete
; =============================================

(define eval-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (un-programa (body)
        (car (eval-expression body (empty-env)))))))

(define flowlang
  (lambda (string)
    (let ((pgm (scan&parse-flowlang string)))
      (eval-program pgm))))


(define start-flowlang-repl
  (sllgen:make-rep-loop
    "--> "
    (lambda (pgm) (eval-program pgm))
    (sllgen:make-stream-parser scanner-spec-flowlang grammar-flowlang)))

(start-flowlang-repl)

