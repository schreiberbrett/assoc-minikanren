#lang racket

; A variant of miniKanren which supports a new constraint:
;
; assoco - associate a key with a value.
;
; Similar to how classic unification either succeds once or
; fails, assoco either succeeds once or fails the "key
; check".
;
; This version of miniKanren requires a state which holds a
; substitution S and and association A.
(define (assoco k v)
  (lambda (st)
    (let* ([S (S-of st)]
           [A (A-of st)]
           [st (key-check
                (make-st S (cons `(,k . ,v) A)))])
      (if st `(,st) '()))))


; The association's only invariant is that two entries which
; mention the same key must have equal values. This check is
; performed whenever "==" and "assoco" update the
; substitution or association, respectively.
;
; key-check: State -> Maybe State
(define (key-check st)
  ; First, walk* the entries in the association and store
  ; them in a vector.
  (let* ((S (S-of st))
         (A (A-of st))
         (n (length A))
         (vect (list->vector
                (map (lambda (k/v) (walk* k/v S)) A))))


    ; For any two walked entries (ignoring known duplicates),
    ; if the keys are the same, then the values must be
    ; unified
    (let loop-i ((i 0))
      (if (= i n)
          st
          (let* ((k1/v1 (vector-ref vect i))
                 (k1 (car k1/v1))
                 (v1 (cdr k1/v1)))
            (let loop-j ((j 0))
              (if (= j i)
                  (loop-i (+ i 1))
                  (let* ((k2/v2 (vector-ref vect j))
                         (k2 (car k2/v2))
                         (v2 (cdr k2/v2)))
                    (if (and (eqv? k1 k2)
                             (not (eqv? v1 v2)))
                        (unify v1 v2 st)
                        (loop-j (+ j 1)))))))))))



; The rest of the code is derived from "The Reasoned Schemer,
; 2nd Edition" found here:
; https://github.com/TheReasonedSchemer2ndEd/CodeFromTheReasonedSchemer2ndEd/blob/master/trs2-impl.scm
; 
; With additional modifications inspired by Joshi & Byrd 2018,
; A Tutorial Reconstruction of miniKanren with Constraints
; https://drive.google.com/file/d/1svTPpIowx4InQIaUU3DyVEMpcoSZP6Bm/view



; TRS2e license:

;;; Copyright © 2018 Daniel P. Friedman, William E. Byrd, Oleg Kiselyov, and Jason Hemann
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


; The state is more than just a substitution. Like in Joshi &
; Byrd, it is a list. The car is the familiar association-list
; substitution. The cadr is an association list from terms to
; terms.
(define (make-st S A)
  `(,S ,A))

(define (S-of st)
  (car st))

(define (A-of st)
  (cadr st))

(define empty-st (make-st '() '()))


; Like TRS2e, use pointer comparison rather than a counter of
; logic variables.
(define var (lambda (x) (vector x)))
(define var? (lambda (x) (vector? x)))

(define (walk v S)
  (let ((a (and (var? v) (assv v S))))
    (cond
      ((pair? a) (walk (cdr a) S))
      (else v))))



; Extend the substitution in state. Since the state is a pair
; whose car is the substitution, the extended substitution is
; part of a new state pair.
;
; Like in TRS2e, the occurs check causes this operation to
; fail. But there is also a new way to fail: the extended
; state may invalidate the association constraints. So
; 'key-check' is needed.
(define (ext-s x v st)
  (let ([S (S-of st)]
        [A (A-of st)])
    (cond
      ((occurs? x v S) #f)
      (else (key-check
             (make-st (cons `(,x . ,v) S) A))))))


; The occurs check as defined in TRS2e, but missing from J&B
(define (occurs? x v S)
  (let ((v (walk v S)))
    (cond
      ((var? v) (eqv? v x))
      ((pair? v) 
       (or (occurs? x (car v) S)
           (occurs? x (cdr v) S)))
      (else #f))))

(define (unify u v st)
  (let* ([S (S-of st)]
         [u (walk u S)]
         [v (walk v S)])
    (cond
      ((eqv? u v) st)
      ((var? u) (ext-s u v st))
      ((var? v) (ext-s v u st))
      ((and (pair? u) (pair? v))
       (let ((st (unify (car u) (car v) st)))
         (and st
              (unify (cdr u) (cdr v) st))))
      (else #f))))

(define (== u v)
  (lambda (st)
    (let ((st (unify u v st)))
      (if st `(,st) '()))))

(define succeed
  (lambda (st)
    `(,st)))
 
(define fail
  (lambda (st)
    '()))

(define (disj2 g1 g2)
  (lambda (st)
    (append-inf (g1 st) (g2 st))))

(define (append-inf s-inf t-inf)
  (cond
    ((null? s-inf) t-inf)
    ((pair? s-inf) 
     (cons (car s-inf)
       (append-inf (cdr s-inf) t-inf)))
    (else (lambda () 
            (append-inf t-inf (s-inf))))))

(define (take-inf n s-inf)
  (cond
    ((and n (zero? n)) '())
    ((null? s-inf) '())
    ((pair? s-inf) 
     (cons (car s-inf)
       (take-inf (and n (sub1 n))
         (cdr s-inf))))
    (else (take-inf n (s-inf)))))

(define (conj2 g1 g2)
  (lambda (s)
    (append-map-inf g2 (g1 s))))

(define (append-map-inf g s-inf)
  (cond
    ((null? s-inf) '())
    ((pair? s-inf)
     (append-inf (g (car s-inf))
       (append-map-inf g (cdr s-inf))))
    (else (lambda () 
            (append-map-inf g (s-inf))))))

(define (call/fresh name f)
  (f (var name)))

(define (reify-name n)
  (string->symbol
    (string-append "_"
      (number->string n))))

(define (walk* v S)
  (let* ((v (walk v S)))
    (cond
      ((var? v) v)
      ((pair? v)
       (cons
         (walk* (car v) S)
         (walk* (cdr v) S)))
      (else v))))

(define-syntax project
  (syntax-rules ()
    ((project (x ...) g ...)
     (lambda (st)
       (let ((x (walk* x (S-of st))) ...)
         ((conj g ...) st))))))


; Reification changes inspired by Joshi & Byrd 2018.

; The result of a call to run or run* produces a reified
; output. In J&B, these are side conditions. Here, the only
; side condition is the association. It is reified from the
; same substitution as the initial var, with unique entries
; in lexicographic order.
(define (reify-S v r)
  (let ((v (walk v r)))
    (cond
      ((var? v)
       (let ((n (length r)))
         (let ((rn (reify-name n)))
           (cons `(,v . ,rn) r))))
      ((pair? v)
       (let ((r (reify-S (car v) r)))
         (reify-S (cdr v) r)))
      (else r))))

(define (reify v)
  (lambda (st)
    (let ((S (S-of st))
          (A (A-of st)))
      (let ((v (walk* v S))
            (A (walk* A S)))
        (let ((r (reify-S `(,v ,A) '())))
          (let ((v (walk* v r))
                (A (walk* A r)))
            `(,v ,(unique (sort (drop-dot A) lex<?)))))))))


(define (unique sorted-lst)
  (cond
    ((null? sorted-lst) '())
    ((null? (cdr sorted-lst)) sorted-lst)
    ((equal? (car sorted-lst) (cadr sorted-lst)) (unique (cdr sorted-lst)))
    (else (cons (car sorted-lst) (unique (cdr sorted-lst))))))

(define (lex<? t1 t2)
  (let ([t1 (datum->string t1)]
        [t2 (datum->string t2)])
    (string<? t1 t2)))

(define (datum->string d)
  (let ([op (open-output-string)])
    (begin (display d op)
           (get-output-string op))))

(define (drop-dot A)
  (map (lambda (x) `(,(car x) ,(cdr x))) A))


(define (run-goal n g)
  (take-inf n (g empty-st)))

(define (ifte g1 g2 g3)
  (lambda (s)
    (let loop ((s-inf (g1 s)))
      (cond
        ((null? s-inf) (g3 s))
        ((pair? s-inf)
         (append-map-inf g2 s-inf))
        (else (lambda ()
                (loop (s-inf))))))))

(define (once g)
  (lambda (s)
    (let loop ((s-inf (g s)))
      (cond
        ((null? s-inf) '())
        ((pair? s-inf)
         (cons (car s-inf) '()))
        (else (lambda ()
                (loop (s-inf))))))))

(define-syntax disj
  (syntax-rules ()
    ((disj) fail)
    ((disj g) g)
    ((disj g0 g ...) (disj2 g0 (disj g ...)))))

(define-syntax conj
  (syntax-rules ()
    ((conj) succeed)
    ((conj g) g)
    ((conj g0 g ...) (conj2 g0 (conj g ...)))))

(define-syntax defrel
  (syntax-rules ()
    ((defrel (name x ...) g ...)
     (define (name x ...)
       (lambda (s)
         (lambda ()
           ((conj g ...) s)))))))

(define-syntax run
  (syntax-rules ()
    ((run n (x0 x ...) g ...)
     (run n q (fresh (x0 x ...)
                (== `(,x0 ,x ...) q) g ...)))
    ((run n q g ...)
     (let ((q (var 'q)))
       (map (reify q)
         (run-goal n (conj g ...)))))))

(define-syntax run*
  (syntax-rules ()
    ((run* q g ...) (run #f q g ...))))

(define-syntax fresh
  (syntax-rules ()
    ((fresh () g ...) (conj g ...))
    ((fresh (x0 x ...) g ...)
     (call/fresh 'x0
       (lambda (x0)
         (fresh (x ...) g ...))))))

(define-syntax conde
  (syntax-rules ()
    ((conde (g ...) ...)
     (disj (conj g ...) ...))))

(define-syntax conda
  (syntax-rules ()
    ((conda (g0 g ...)) (conj g0 g ...))
    ((conda (g0 g ...) ln ...)
     (ifte g0 (conj g ...) (conda ln ...)))))

(define-syntax condu
  (syntax-rules ()
    ((condu (g0 g ...) ...)
     (conda ((once g0) g ...) ...))))
