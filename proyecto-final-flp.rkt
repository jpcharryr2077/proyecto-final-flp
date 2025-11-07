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

; Ambiente
(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?)
    (val expval?)
    (old-env environment?))
  (extend-env-rec
    (vars (list-of symbol?))
    (exps (list-of expression?))
    (old-env environment?)))

; Buscar variable en ambiente
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "Variable no definida: ~s" search-var))
      (extend-env (saved-var saved-val saved-env)
        (if (eq? saved-var search-var)
            saved-val
            (apply-env saved-env search-var)))
      (extend-env-rec (vars exps old-env)
        (let loop ((vars vars) (exps exps))
          (if (null? vars)
              (apply-env old-env search-var)
              (if (eq? (car vars) search-var)
                  (proc-val (procedure (car vars) (car exps) env))
                  (loop (cdr vars) (cdr exps)))))))))

; Evaluador básico
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (var-decl-exp (var val-exp)
        (let ((val (eval-expression val-exp env)))
          (extend-env var val env)
          val))
      (assign-exp (var val-exp)
        (let ((val (eval-expression val-exp env)))
          ; En una implementación completa, actualizaríamos el ambiente
          val))
      (if-exp (cond-exp true-exp false-exp)
        (let ((cond-val (eval-expression cond-exp env)))
          (if (cases expval cond-val
                (bool-val (b) b)
                (num-val (n) (not (zero? n)))
                (null-val () #f)
                (else #t))
              (eval-expression true-exp env)
              (eval-expression false-exp env))))
      (begin-exp (exps)
        (if (null? exps)
            (null-val)
            (let loop ((exps exps) (result (null-val)))
              (if (null? exps)
                  result
                  (loop (cdr exps) (eval-expression (car exps) env))))))
      (else (eopl:error 'eval-expression "Expresión no implementada: ~s" exp)))))

;=================================================================================
; Prueba de números
;(eval-expression (const-exp 42) (empty-env))
; → (num-val 42)

; Prueba de if verdadero
;(eval-expression (if-exp (const-exp 1) (const-exp 10) (const-exp 20)) (empty-env))
; → (num-val 10)

; Prueba de if falso
;(eval-expression (if-exp (const-exp 0) (const-exp 10) (const-exp 20)) (empty-env))
; → (num-val 20)

; Prueba de begin
;(eval-expression (begin-exp (list (const-exp 1) (const-exp 2) (const-exp 3))) (empty-env))
; → (num-val 3)