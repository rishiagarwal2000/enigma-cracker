#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         (prefix-in utils: "utils.rkt")
         (prefix-in stats: "statistics.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                     ;;
;; Strategies                                                                          ;;
;; ==========                                                                          ;;
;; For the purpose of this assignment, just the `etai` strategy is expected, since     ;;
;; we have dictionary-closure and secret-word-enumeration to leap-frog to the right    ;;
;; key. This technique would fail for harder keys which are arbitrary permutations of  ;;
;; the alphabet. We will be forced to explore many more strategies (along with         ;;
;; dictionary-closure of course).                                                      ;;
;;                                                                                     ;;
;; Strategies to guess substitutions for the key using statistical information about   ;;
;; - the English language from utils.rkt                                               ;;
;; - the cipher text      from statistics.rkt                                          ;;
;;                                                                                     ;;
;; Follow the function signature as indicated below. Deviations will make it           ;;
;; impossible for automatic grading of your submission.                                ;;
;; Moreover, we do not expect your strategies to require any more/different            ;;
;; arguments. Note that you recieve the key as argument, so you can at the very        ;;
;; least ensure that all the substitutions are monoalphabetic wrt this key.            ;;
;;                                                                                     ;;
;; Signature:                                                                          ;;
;; ```                                                                                 ;;
;; (define (my-fundoo-strategy key)                                                    ;;
;;   ;; Make use of `utils:ciphertext`, `utils:cipher-word-list`                       ;;
;;   ...)                                                                              ;;
;; ```                                                                                 ;;
;;                                                                                     ;;
;; Substitutions                                                                       ;;
;; -------------                                                                       ;;
;; In order to extend the key incrementally, we use `utils:add-substitution` to        ;;
;; extend a given key with a substitution.                                             ;;
;;                                                                                     ;;
;; A substitution is a list of pairs, each pair mapping a plaintext char to a          ;;
;; ciphertext char. For example, to extend the key with T -> a and O -> r              ;;
;; (simultaneously), we use the substitution:                                          ;;
;; ```                                                                                 ;;
;; (list (cons #\T #\a) (cons #\O #\r))                                                ;;
;; ```                                                                                 ;;
;; For a single substitution use a singleton list (containing just one pair).          ;;
;;                                                                                     ;;
;; **CAUTION**                                                                         ;;
;; -----------                                                                         ;;
;; 1. Note that add-substitution does not do sanity checks on the substitution and use ;;
;;    of `utils:is-monoalphabetic` is recommended to ensure that you don't             ;;
;;    inadvertently create invalid keys.                                               ;;
;; 2. You must provide a list called `compositions` in this module.                    ;;
;;                                                                                     ;;
;; See docs in "utils.rkt" for more information.                                       ;;
;;                                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; You must add "public" functions of this module to this list.
(provide etai
         ;; Some more suggested strategies:
         
         ;; common-words-double
         ;; bigrams
         ;; common-initial-letters
         ;; common-final-letters
         ;; common-words-triple
         ;; trigrams
         ;; common-double-letters
         ;; common-words-quadruple
         ;; quadgrams
         
         ;; lists of strategies
         composition)

;; A strategy that uses some statistical information to generate potential
;; substitutions for E, T, A and I.
;; Refer the assignment manual for tips on developing this strategy. You can
;; interact with our etai with the executable we provide.
(define (listafterkth l k)
  (cond[(< (length l) k) '()]
       [(= k 0)  l]
       [else (listafterkth (cdr l) (- k 1))]))
(define (listbeforekth l k)
  (cond[(< (length l) k) l]
       [(= k 1) '()]
       [else (append (list (car l)) (listbeforekth (cdr l) (- k 1)))]))
(define (slice l a b)
  (listafterkth (listbeforekth l (+ b 1)) (- a 1)))


(define (zip l1 l2)
  (cond [(or (null? l1) (null? l2)) '()]
        [else (cons (cons (car l2) (car l1)) (zip (cdr l1) (cdr l2)))]))
(define (myappend l1 l2)
  (append* (map (lambda (z) (map (lambda (y) (append y z)) l2)) l1)))
(define (combine1 l1 l2)
  (map (lambda (y) (zip y l2)) (append* (map (lambda (g) (permutations g) )(combinations l1 2)))))
(define (combine2 l1 l2)
  (map (lambda (y) (zip y l2)) (append* (map (lambda (g) (permutations g) )(combinations l1 3)))))
(define (combine3 l1 l2)
  (map (lambda (y) (zip y l2)) (append* (map (lambda (g) (permutations g) )(combinations l1 4)))))
;;output should be subs-list instead of key-list
(define (etai key)
  (define (etai-helper word-list ciphertext)
    (let ([one-letter-words (map (lambda (z) (car (string->list z))) (stats:cipher-common-words-single word-list))])
      (cond[(= (length one-letter-words) 2) (myappend (combine1 one-letter-words (list #\A #\I))
                                            (combine1 (remove* one-letter-words (listbeforekth (stats:cipher-monograms ciphertext) 6)) (list #\E #\T)))]
           [(= (length one-letter-words) 1) (append (myappend (cons one-letter-words #\A)
                                            (combine2 (remove* one-letter-words (listbeforekth (stats:cipher-monograms ciphertext) 11)) (list #\E #\T #\I)))
                                            (myappend (cons one-letter-words #\I)
                                            (combine2 (remove* one-letter-words (listbeforekth (stats:cipher-monograms ciphertext) 11)) (list #\E #\T #\A))))]
           [else (combine3 (listbeforekth (stats:cipher-monograms ciphertext) 13) (list #\E #\T #\A #\I))])))
   (filter (lambda (z) (utils:is-monoalphabetic? z key)) (etai-helper utils:cipher-word-list utils:ciphertext)))

;; A suggested composition of strategies that might work well. Has not been
;; exhaustively tested by us. Be original ;)
(define composition (list etai))
                  ;; common-words-double
                  ;; bigrams
                  ;; common-initial-letters
                  ;; common-final-letters
                  ;; common-words-triple
                  ;; trigrams
                  ;; common-double-letters))
                  ;; common-words-quadruple
                  ;; quadgrams))

