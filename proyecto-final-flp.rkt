#lang eopl
;******************************************************************************************
; Proyecto final de curso - Flowlang
; Integrantes:
;[Juan Felipe Palechor 2270963]
;[Juan Esteban Rodriguez 2042282]
;[Juan Pablo Charry 2040579]
; Curso: Fundamentos de Lenguajes de Programación
; Profesor: Robinson Duque
; URL del repositorio: [https://github.com/jpcharryr2077/proyecto-final-flp.git]
;******************************************************************************************

; Definición de tipos de valores
(define-datatype expval expval?
  (num-val
    (value number?))
  (bool-val
    (value boolean?))
  (str-val
    (value string?))
  (null-val)
  (proc-val
    (value proc?))
  (list-val
    (value list?))
  (dict-val
    (value list?))) ; lista de pares (clave . valor)

; Definición de procedimientos
(define-datatype proc proc?
  (procedure
    (vars (list-of symbol?))
    (body expression?)
    (env environment?)))

; Expresiones
(define-datatype expression expression?
  (const-exp
    (num number?))
  (var-exp
    (var symbol?))
  (var-decl-exp
    (var symbol?)
    (val-exp expression?))
  (assign-exp
    (var symbol?)
    (val-exp expression?))
  (if-exp
    (cond-exp expression?)
    (true-exp expression?)
    (false-exp expression?))
  (begin-exp
    (exps (list-of expression?))))

; Store global para manejar mutabilidad
(define the-store 'initial-store-uninitialized)

(define empty-store
  (lambda () '()))

(define get-store
  (lambda () the-store))

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

(define reference?
  (lambda (v)
    (integer? v)))

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
          (letrec ((setref-inner
                   (lambda (store1 ref1)
                     (cond
                       ((null? store1)
                        (eopl:error 'setref "Referencia inválida ~s" ref1))
                       ((zero? ref1)
                        (cons val (cdr store1)))
                       (else
                        (cons (car store1)
                              (setref-inner (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

; Actualizamos el ambiente para usar referencias
(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?)
    (ref reference?)
    (old-env environment?))
  (extend-env-rec
    (p-names (list-of symbol?))
    (b-vars (list-of symbol?))
    (bodies (list-of expression?))
    (old-env environment?)))

; Actualizamos apply-env
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "Variable no definida: ~s" search-var))
      (extend-env (saved-var saved-ref saved-env)
        (if (eq? saved-var search-var)
            (deref saved-ref)
            (apply-env saved-env search-var)))
      (extend-env-rec (p-names b-vars p-bodies saved-env)
        (cond
          ((member search-var p-names)
           (let ((index (list-index (lambda (x) (eq? x search-var)) p-names)))
             (proc-val (procedure 
                       (list-ref b-vars index) 
                       (list-ref p-bodies index) 
                       env))))
          (else
           (apply-env saved-env search-var)))))))

; Función auxiliar para encontrar índice en lista
(define list-index
  (lambda (pred lst)
    (let loop ((lst lst) (i 0))
      (cond
        ((null? lst) #f)
        ((pred (car lst)) i)
        (else (loop (cdr lst) (+ i 1)))))))

; CAMBIO PRINCIPAL: eval-expression ahora retorna (valor . nuevo-ambiente)
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (cons (num-val num) env))
      
      (var-exp (var) (cons (apply-env env var) env))
      
      (var-decl-exp (var val-exp)
        (let* ((val-env (eval-expression val-exp env))
               (val (car val-env))
               (new-env (cdr val-env))
               (ref (newref val)))
          (cons val (extend-env var ref new-env))))
      
      (assign-exp (var val-exp)
        (let* ((val-env (eval-expression val-exp env))
               (val (car val-env))
               (current-env (cdr val-env)))
          ; Buscar la variable en el ambiente y actualizarla
          (letrec ((find-and-update
                    (lambda (env)
                      (cases environment env
                        (empty-env ()
                          (eopl:error 'assign-exp "Variable no definida: ~s" var))
                        (extend-env (saved-var saved-ref saved-env)
                          (if (eq? saved-var var)
                              (begin
                                (setref! saved-ref val)
                                (cons val env))
                              (find-and-update saved-env)))
                        (extend-env-rec (p-names b-vars p-bodies saved-env)
                          (find-and-update saved-env))))))
            (find-and-update current-env))))
      
      (if-exp (cond-exp true-exp false-exp)
        (let* ((cond-env (eval-expression cond-exp env))
               (cond-val (car cond-env))
               (cond-env-updated (cdr cond-env)))
          (if (cases expval cond-val
                (bool-val (b) b)
                (num-val (n) (not (zero? n)))
                (null-val () #f)
                (else #t))
              (eval-expression true-exp cond-env-updated)
              (eval-expression false-exp cond-env-updated))))
      
      (begin-exp (exps)
        (if (null? exps)
            (cons (null-val) env)
            (let loop ((exps exps) (current-env env) (result (null-val)))
              (if (null? exps)
                  (cons result current-env)
                  (let* ((exp-env (eval-expression (car exps) current-env))
                         (exp-val (car exp-env))
                         (new-env (cdr exp-env)))
                    (loop (cdr exps) new-env exp-val))))))
      
      (else (eopl:error 'eval-expression "Expresión no implementada: ~s" exp)))))

; Función helper para extraer solo el valor (para pruebas)
(define eval-exp-value
  (lambda (exp env)
    (car (eval-expression exp env))))

; Función helper para extraer solo el ambiente (para pruebas)  
(define eval-exp-env
  (lambda (exp env)
    (cdr (eval-expression exp env))))

; Inicializar store
(initialize-store!)

;======================== Pruebas ===========================
;(define env0 (empty-env))

; 1. Crear variable
;(define r1 (eval-expression (var-decl-exp 'x (const-exp 5)) env0))
;(car r1)        ; → (num-val 5)
;(define env1 (cdr r1))

; 2. Leer variable  
;(car (eval-expression (var-exp 'x) env1))  ; → (num-val 5)

; 3. Modificar variable
;(define r3 (eval-expression (assign-exp 'x (const-exp 10)) env1))
;(car r3)        ; → (num-val 10)

; 4. Verificar cambio
;(car (eval-expression (var-exp 'x) env1))  ; → (num-val 10)
