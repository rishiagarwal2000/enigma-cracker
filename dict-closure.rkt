#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt"))

(provide dictionary-closure)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                  ;;
;; Dictionary Closure                                                               ;;
;; ==================                                                               ;;
;;                                                                                  ;;
;; A choice of substitution can really trigger more substitutions by looking at the ;;
;; partially decrypted text - surely there will be some words which can be uniquely ;;
;; determined using the dictionary. It is prudent to concretize this "choice" as    ;;
;; this purely deterministic (involving absolutely no guess-work). In more          ;;
;; technical terms, this is called "maintaining arc-consistency" (look it up on     ;;
;; Wikipedia).                                                                      ;;
;;                                                                                  ;;
;; This function must utilise the dictionary and the cipher-word-list. Decrypt each ;;
;; word (`utils:decrypt`) and check if the dictionary has:                          ;;
;;                                                                                  ;;
;; 1. a unique completetion!                                                        ;;
;;    - Extend your key using the information with this match. Continue exploring   ;;
;;      the words under the extended key.                                           ;;
;; 2. many completions.                                                             ;;
;;    - Do nothing, just continue exploring the words under the same key. If none   ;;
;;      of the words fall into (1), return with the key that you have built so far. ;;
;; 3. no completions!                                                               ;;
;;    - Return `#f` (false), indicating that this partial key is wrong, and we must ;;
;;      revert to the original key.                                                 ;;
;;                                                                                  ;;
;; Returns either of:                                                               ;;
;; a. a (possibly) extended-key.                                                    ;;
;; b. `#f` if this key led to case (3) for some word.                               ;;
;;                                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (sanitize-text ciphertext)
  (regexp-replace* (pregexp "'\\w+") ciphertext ""))
(define (find-common lst)
  (define (is-present1? a l)
    (cond[(null? l) #f]
         [(equal? a (car l)) #t]
         [else (is-present1? a (cdr l))]))
  (define (helper a l)
    (cond[(null? l) #t]
         [else (and (is-present1? a (car l)) (helper a (cdr l)))]))
  (define (helper1 l)
    (cond[(null? (car l)) '()]
         [(helper (caar l) (cdr l)) (cons (caar l) (helper1 (cons (cdar l) (cdr l))))]
         [else (helper1 (cons (cdar l) (cdr l)))]))
  (helper1 lst))


(define (bijective-list a b)
  (define (helper l1 l2 key)
  (cond [(null? l1) #t]
        [(char-upper-case? (car l1)) (and (equal? (car l1) (car l2)) (helper (cdr l1) (cdr l2) key))]
        [else (let ([is-present (find (car l1) key)])
         (if is-present (and (equal? is-present (car l2)) (helper (cdr l1) (cdr l2) key))
                  (helper (cdr l1) (cdr l2) (cons (cons (car l2) (car l1)) key))))]))
  (helper a b '()))
(define (is-present? a l)
  (cond[(null? l) #f]
       [(equal? (cdar l) a) #t]
       [else (is-present? a (cdr l))]))
(define (find a l)
  (cond[(null? l) #f]
       [(equal? (cdar l) a) (caar l)]
       [else (find a (cdr l))]))
(define (find-key str dict-str)
  (define (key-helper l1 l2 key)
    (cond[(null? l1) key]
         [(char-upper-case? (car l1)) (key-helper (cdr l1) (cdr l2) key)]
         [else (if (is-present? (car l1) key) (key-helper (cdr l1) (cdr l2) key) 
                   (key-helper (cdr l1) (cdr l2) (cons (cons (car l2) (car l1)) key)))]))
  (key-helper (string->list str) (string->list dict-str) '()))


(define (dict-word? str)
  (define (helper-f dict-str)
    (and (= (string-length str) (string-length dict-str))  (bijective-list (string->list str) (string->list dict-str))))
  (filter helper-f utils:dictionary))
(define (consistent-dict-word-key-list str  key match-dict-list)
  (define (helper str word-list)
    (cond [(null? word-list) '()]
          [else (let ([subs1 (find-key str (car word-list))])
                  (if (utils:is-monoalphabetic? subs1 key) (cons subs1 (helper str (cdr word-list)))
                      (helper str (cdr word-list))))]))
    (helper str match-dict-list))

(define (dict-closure-helper decrypted-word-list key)
  (define (helper1 decrypted-list dict-list act-key)
  (cond[(null? decrypted-list) act-key]
       [else (let* ([match-dict-list (dict-word? (car decrypted-list))]
                    [subs-list (consistent-dict-word-key-list (car decrypted-list) act-key match-dict-list)])
               (cond [(> (length subs-list) 1) (let ([common-subs-list (find-common subs-list)])
                                                 (if (pair? common-subs-list) (let ([keyf (utils:add-substitution common-subs-list act-key)])
                                                                                (dict-closure-helper (map
                                                                           (lambda (y) (utils:decrypt keyf y))
                                                                           (remove* (list (car decrypted-list)) decrypted-word-list))
                                                                          keyf))
                                                     (helper1 (cdr decrypted-list) dict-list act-key)))]
                     [(= (length subs-list) 1) (let ([keyf (utils:add-substitution (car subs-list) act-key)])
                                                     (dict-closure-helper (map
                                                                           (lambda (y) (utils:decrypt keyf y))
                                                                           (remove* (list (car decrypted-list)) decrypted-word-list))
                                                                          keyf))]
                     [(> (length match-dict-list) 0) (helper1 (cdr decrypted-list) dict-list act-key)]
                     [else #f]))]))
  (helper1 decrypted-word-list utils:dictionary key))  

(define (dictionary-closure key) 
  (dict-closure-helper (map (lambda (y) (utils:decrypt key y)) utils:cipher-word-list) key))
