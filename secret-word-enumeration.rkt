#lang racket/base

;; You can require more modules of your choice.
(require racket/string
         racket/list
         (prefix-in utils: "utils.rkt"))

(provide secret-word-enumeration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                           ;;
;; Secret Word Enumeration                                                                   ;;
;; =======================                                                                   ;;
;;                                                                                           ;;
;; This step exploits the fact that all keys begin with a secret word that is a              ;;
;; proper SIX-LETTER word from the English dictionary.                                       ;;
;;                                                                                           ;;
;; Given a partial key, we can query the dictionary for a list of 6 letter words             ;;
;; that can potentially begin the key.                                                       ;;
;; We can then filter out potential candidates whose keys do not agree with our partial key. ;;
;;                                                                                           ;;
;; It is possible that given a (wrong) partial key, we discover that none of these           ;;
;; potential candidates can agree with our partial key. This really implies a                ;;
;; mistake in the choice of substitution, since dictionary-closure is completely             ;;
;; deterministic (modulo any bugs in your implementation :)                                  ;;
;;                                                                                           ;;
;; Hence, this function must return either of:                                               ;;
;; a. `#f` if there are no consistent candidates for this key.                               ;;
;; b. the original key if there are multiple consistent candidates.                          ;;
;; c. the complete key if there's only one consistent candidate!                             ;;
;;                                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (list-before-kth l k)
  (cond[(< (length l) k) l]
       [(= k 1) '()]
       [else (append (list (car l)) (list-before-kth (cdr l) (- k 1)))]))
(define (find a l)
  (cond [(null? l) #f]
        [(equal? a (car l)) #t]
        [else (find a (cdr l))]))
(define (make-dup key)
  (cond[(null? key) '()]
       [(not (equal? (car key) #\_)) (cons (char-upcase (car key)) (make-dup (cdr key)))]
       [else (make-dup (cdr key))]))
(define (bijection2 lst1 lst2 acc)
  (define (helper l1 l2 duplicate-acc)
  (cond[(null? l1) #t]
       [(equal? (car l1) #\_) (if (find (car l2) duplicate-acc) #f
                                  (helper (cdr l1) (cdr l2) (cons (car l2) duplicate-acc)))]
       [else (and (equal? (char-upcase (car l1)) (car l2)) (helper (cdr l1) (cdr l2) duplicate-acc))]))
  (helper lst1 lst2 acc))
(define (g l1 l2 acc)
  (and (= (length l1) (length l2)) (bijection2 l1 l2 acc)))
(define (swe-helper l dict-list acc)
  (filter (lambda (y) (g l (string->list y) acc)) dict-list))
(define (myequal? l1 l2)
  (cond [(null? l1) #t]
        [(equal? (car l2) #\_) (myequal? (cdr l1) (cdr l2))]
        [else (and (equal? (car l1) (car l2)) (myequal? (cdr l1) (cdr l2)))]))
        
  
(define (secret-word-enumeration key-after-dictionary-closure) ;; Returns a key or false (#f)
  (define (filt-replace p)
  (cond [(null? p) '()]
        [else (let ([r (utils:encryption-key (car p))])
                (if (myequal? r key-after-dictionary-closure) (cons r (filt-replace (cdr p)))
                    (filt-replace (cdr p))))]))
  
  (let* ([p (swe-helper (list-before-kth key-after-dictionary-closure 7) utils:dictionary (make-dup key-after-dictionary-closure))]
        [q (filt-replace p)])
    (cond [(= (length q) 1) (car q)]
          [(> (length q) 1) key-after-dictionary-closure]
          [else #f])))

