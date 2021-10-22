#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                 ;;
;; Ciphertext Statistics                                                           ;;
;; =====================                                                           ;;
;;                                                                                 ;;
;; The module should provide a bunch of functions that do statistical analysis of  ;;
;; ciphertext. The output is almost always just an ordered list (counts are        ;;
;; omitted).                                                                       ;;
;;                                                                                 ;;
;; Fill in the body for the skeletons and do not change the arguments. You can     ;;
;; define as many functions as you require, there's no special credit for          ;;
;; implementing/using all of them.                                                 ;;
;;                                                                                 ;;
;; CAUTION:                                                                        ;;
;; 1. Be mindful that bi, tri and quadgrams do not cross word boundaries. Hence,   ;;
;; you must process each word separately.                                          ;;
;;                                                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Analyses
(provide cipher-monograms
         cipher-bigrams
         cipher-neighbourhood
         cipher-trigrams
         cipher-quadgrams
         cipher-common-words-single
         cipher-common-words-double
         cipher-common-words-triple
         cipher-common-words-quadruple
         cipher-common-initial-letters
         cipher-common-final-letters
         cipher-common-double-letters
         ;; any other functions of your design come below:

         ;; my-fundoo-analysis
         )

;; Takes ciphertext and produces a list of cipher chars sorted in decreasing
;; order of frequency.
(define (order l)
  (sort (lst l) > #:key cdr))
(define (lst l)
  (cond [(null? l) l]
       [else (cons (cons (car l) (count (lambda (x) (equal? x (car l))) l)) (lst (remove* (list (car l)) l)))]))
(define (descending-freq l)
  (map (lambda (z) (car z)) (order l)))
(define (cipher-monograms ciphertext)
  (descending-freq (remove* (list #\space #\. #\, #\? #\! #\newline #\' #\; #\-) (string->list ciphertext))))

;; Takes the cipher-word-list and produces a list of 2-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (form-x-grams x z)
  (cond [(< (string-length z) x) '()]
                                  [else (let ([s (substring z 0 x)])
                                          (cons s (form-x-grams x (string-trim z (substring z 0 1) #:right? #f))))]))

(define (cipher-bigrams cipher-word-list)
  (descending-freq (append* (map (lambda (z) (form-x-grams 2 z))
             cipher-word-list))))

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter.
;;
;; Takes a optional keyword argument `mode`:
;; 1. (cipher-neighbourhood cipher-bigrams #:mode 'predecessor)
;;    - Count only those occurrences where the (given) char is preceeds other
;;      char.
;; 2. (cipher-neighbourhood cipher-bigrams #:mode 'successor)
;;    - Count only those occurrences where the (given) char is succeeds other
;;      char.
;; 3. (cipher-neighbourhood cipher-bigrams #:mode 'both)
;;    - Count all occurrences where the (given) char neighbours the other
;;      char.
;;
;; The output is a list of pairs of cipher char and the count of it's
;; neighbours. The list must be in decreasing order of the neighbourhood count.
(define (form-one-letter bigrams)
  (cond[(null? bigrams) '()]
       [else (let* ([x (car bigrams)]
                   [z (string->list x)])
                   (cons (car z) (cons (cadr z) (form-one-letter (cdr bigrams)))))]))
(define (no-duplicate-single-letter bigrams)
  (remove-duplicates (form-one-letter bigrams)))
(define (norder l)
  (sort l > #:key cdr))
(define (pred l)
  (define (helper lst)
    ;(displayln lst)
    (cond[(null? lst) '()]
         [else (let* ([r (substring (car lst) 0 1)] [z (car (string->list (car lst)))] [q (filter (lambda (y) (string-prefix? y r)) lst)])
          (cons (cons z (length q)) (helper (remove* q lst))))]))
  (norder (helper l)))
(define (succ l)
  (define (helper lst)
    ;(displayln lst)
    (cond[(null? lst) '()]
         [else (let* ([r (substring (car lst) 1 2)] [z (cadr (string->list (car lst)))] [q (filter (lambda (y) (string-suffix? y r)) lst)])
          (cons (cons z (length q)) (helper (remove* q lst))))]))
  (norder (helper l)))
(define (pred1 l)
  (define (helper lst)
    (cond[(null? lst) '()]
         [else (let* ([r (substring (car lst) 0 1)] [z (car (string->list (car lst)))] [q (filter (lambda (y) (string-prefix? y r))  lst)]
                                                    [q1 (filter (lambda (y) (string-prefix? y r) ) lst)])
          (cons (cons z (length q)) (helper (remove* q1 lst))))]))
  (norder (helper l)))
(define (succ1 l)
  (define (helper lst)
    (cond[(null? lst) '()]
         [else (let* ([r (substring (car lst) 1 2)] [z (cadr (string->list (car lst)))] [q (filter (lambda (y) (and (string-suffix? y r) (not (string-prefix? y r)))) lst)]
                                                    [q1 (filter (lambda (y) (string-suffix? y r) ) lst)])
          (cons (cons z (length q)) (helper (remove* q1 lst))))]))
  (norder (helper l)))
(define (mysum l1 l2)
  (cond[(null? l1) l2]
       [else (let ([p (find-match (car l1) l2)])
               (if p (cons (cons (caar l1) (+ (cdar l1) (cdr p))) (mysum (cdr l1) (remove* (list p) l2)))
                   (cons (car l1) (mysum (cdr l1) l2))))]))
(define (find-match pair l)
  (cond [(null? l) #f]
        [(equal? (car pair) (caar l)) (car l)]
        [else (find-match pair (cdr l))]))
(define (unique-both l)
  (norder (mysum (succ1 l) (pred1 l))))
(define (not-unique-both l)
  (norder (mysum (succ l) (pred l))))
  
(define (cipher-unique-neighbourhood cipher-bigrams-list mode)
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  
(cond [(equal? mode 'predecessor) (pred cipher-bigrams-list)]
      [(equal? mode 'successor) (succ cipher-bigrams-list)]
      [(equal? mode 'both) (unique-both cipher-bigrams-list)]))

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter, but counts each
;; occurrence distinctly. This comment contains 6 bigrams with "w", all with "i" or "h".
;; So "w" has:
;; when mode is 'both,        6 neighbours
;; when mode is 'predecessor, 6 neighbours
;; when mode is 'successor,   0 neighbours
(define (cipher-neighbourhood cipher-bigrams-list mode)
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  (cond [(equal? mode 'predecessor) (pred cipher-bigrams-list)]
      [(equal? mode 'successor) (succ cipher-bigrams-list)]
      [(equal? mode 'both) (unique-both cipher-bigrams-list)]))


       
  
  
  
  ;; You must match against or test for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  

;; Takes the cipher-word-list and produces a list of 3-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-trigrams cipher-word-list)
  (descending-freq (append* (map (lambda (z) (form-x-grams 3 z))
             cipher-word-list))))

;; Takes the cipher-word-list and produces a list of 4-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-quadgrams cipher-word-list)
  (descending-freq (append* (map (lambda (z) (form-x-grams 4 z))
             cipher-word-list))))

;; Takes the cipher word list and produces a list of single letter words, sorted
;; in decreasing order of frequency. Each element must be a string!
(define (n-letter-words n str-list)
  (filter (lambda (z) (= (string-length z) n)) str-list))
(define (cipher-common-words-single cipher-word-list)
  (descending-freq (n-letter-words 1 cipher-word-list)))

;; Takes the cipher word list and produces a list of double letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-double cipher-word-list)
  (descending-freq (n-letter-words 2 cipher-word-list)))

;; Takes the cipher word list and produces a list of triple letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-triple cipher-word-list)
  (descending-freq (n-letter-words 3 cipher-word-list)))

;; Takes the cipher word list and produces a list of four letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-quadruple cipher-word-list)
  (descending-freq (n-letter-words 4 cipher-word-list)))

;; Takes the cipher word list and produces a list of chars that appear at the
;; start of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (initials str-list)
  (map (lambda (z) (car (string->list z))) str-list))

(define (cipher-common-initial-letters cipher-word-list)
  (descending-freq (initials cipher-word-list)))

;; Takes the cipher word list and produces a list of chars that appear at the
;; end of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (finals str-list)
 (map (lambda (z) (last (string->list z))) str-list))
(define (cipher-common-final-letters cipher-word-list)
  (descending-freq (finals cipher-word-list)))

;; Takes the cipher word list and produces a list of chars that appear as
;; consecutive double letters in some word, sorted in decreasing order of
;; frequency. Each element must thus be a char!
(define (cipher-common-double-letters cipher-word-list)
  '())
