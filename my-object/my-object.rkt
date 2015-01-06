#lang racket/base

(provide object
         object?
         object-extend
         object-fields
         object-ref   object-ref*
         object-set-m object-set-m*
         object-set   object-set*
         send
         this
         )

(require racket/promise
         racket/match
         racket/local
         keyword-lambda/keyword-case-lambda
         kw-utils/keyword-lambda
         syntax/parse/define
         unstable/hash
         racket/stxparam
         "stuff.rkt"
         (for-syntax racket/base
                     syntax/parse
                     ))
(module+ test
  (require rackunit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; structs

(defs-renamed ([-λobject λobject]
               [-object object]
               object?
               object-λobj
               object-fields-promise)
  (defs-renamed ([obj object] [λobj λobject])
    (define object
      (keyword-lambda (kws kw-args ths . rst)
        (keyword-apply object-proc kws kw-args ths rst)))
    (define (λobject ths%)
      (λobject-proc ths%)))
  (struct λobject (hsh)
    #:property prop:procedure λobj)
  (struct object (name λobj fields-promise)
    #:property prop:procedure obj
    #:methods gen:custom-write
    [(define (write-proc obj out mode)
       (obj-write-proc obj out mode))]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; macros

(define-syntax-parameter this #f)

(define-syntax-parser deffld
  [(deffld [id1:id id2:id] ths:id)
   #'(def-var-like-trans id1 #'(object-ref ths 'id2))]
  [(deffld id:id ths:id)
   #'(deffld [id id] ths)])

(define-simple-macro
  (object [field:id expr:expr] ...)
  ((λobject [field expr] ...)))

(define-simple-macro
  (λobject [field:id expr:expr] ...)
  (local [(define (field ths)
            (syntax-parameterize ([this (make-rename-transformer #'ths)])
              (deffld field ths) ...
              expr))
          ...]
    (-λobject (make-immutable-hasheq (list (cons 'field field) ...)))))

(define-simple-macro
  (λobject-extend %-expr:expr
                  (~or (~optional (~seq #:inherit (inherit-id ...)) #:defaults ([(inherit-id 1) '()]))
                       (~optional (~seq #:super ([super-id1 super-id2] ...))
                                  #:defaults ([(super-id1 1) '()]
                                              [(super-id2 1) '()])))
                  ...
                  [field:id expr:expr] ...)
  (local [(define % %-expr)
          (define (field ths)
            (syntax-parameterize ([this (make-rename-transformer #'ths)])
              (define super (λobject-proc %))
              (deffld inherit-id ths) ...
              (deffld [super-id1 super-id2] super) ...
              (deffld field ths) ...
              expr))
          ...]
    (extend-λobject % (make-immutable-hasheq (list (cons 'field field) ...)))))

(define-simple-macro
  (object-extend obj
                 (~or (~optional (~seq #:inherit (inherit-id ...))
                                 #:defaults ([(inherit-id 1) '()]))
                      (~optional (~seq #:super ([super-id1 super-id2] ...))
                                 #:defaults ([(super-id1 1) '()]
                                             [(super-id2 1) '()]))) ...
                 [field:id expr:expr] ...)
  ((λobject-extend (object-λobj obj)
                   #:inherit (inherit-id ...)
                   #:super ([super-id1 super-id2] ...)
                   [field expr] ...)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions

(define (λobject-proc ths%)
  (match-define (-λobject %.hsh) ths%)
  (define flds-promise
    (delay (for/hash ([(k v) (in-hash %.hsh)])
             (values k (v ths)))))
  (define ths
    (-object #f ths% flds-promise))
  (force flds-promise)
  ths)

(define object-proc
  (keyword-case-lambda
   [(obj #:fields _) (object-fields obj)]
   [(obj fld) (object-ref obj fld)]
   [(obj fld #:-> v) (object-set obj fld #:-> v)]
   [(obj fld #:->m m) (object-set-m obj fld #:->m m)]
   [(obj . flds) (apply object-ref* obj flds)]
   [(obj #:-> v fld . flds) (apply object-set* obj #:-> v fld flds)]
   [(obj #:->m m fld . flds) (apply object-set-m* obj #:->m m fld flds)]
   ))

(define (object-fields obj)
  (force (object-fields-promise obj)))

(define (object-ref obj fld)
  (hash-ref (object-fields obj) fld))

(define (object-ref* obj . flds)
  (match flds
    [(list) obj]
    [(cons fld flds)
     (apply object-ref* (object-ref obj fld) flds)]))

(define (object-set-m obj fld #:->m m)
  (define ths% (object-λobj obj))
  (define new-ths% (extend-λobject ths% (hasheq fld m)))
  (new-ths%))

(define (object-set obj fld #:-> v)
  (object-set-m obj fld #:->m (λ (ths) v)))

(define (object-set-m* obj #:->m m fld . flds)
  (match (cons fld flds)
    [(list fld) (object-set-m obj fld #:->m m)]
    [(cons fld rst)
     (define obj.fld (object-ref obj fld))
     (define new-obj.fld (apply object-set-m* obj.fld #:->m m rst))
     (object-set obj fld #:-> new-obj.fld)]))

(define (object-set* obj #:-> v fld . flds)
  (apply object-set-m* obj #:->m (λ (ths) v) fld flds))

(define (send obj method . args)
  (apply (object-ref obj method) args))

(define (extend-λobject % hsh)
  (match-define (-λobject %.hsh) %)
  (-λobject (hash-union %.hsh hsh #:combine (λ (v1 v2) v2))))

(define (obj-write-proc obj out mode)
  (match-define (-object name λobj fields-promise) obj)
  (match mode
    [0  (write-string "(object" out)
        (for ([(k v) (in-hash (force fields-promise))])
          (fprintf out " [~a ~v]" k v))
        (write-string ")" out)
        (void)]
    [_ #:when (symbol? name) (fprintf out "#<object:~a>" name)]
    [_ (write-string "#<object" out)
       (for ([(k v) (in-hash (force fields-promise))])
         (fprintf out " [~a ~v]" k v))
       (write-string ">" out)
       (void)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test-case "simple"
    (define obj
      (object [a 1] [b 2] [c 3]))
    (check-pred object? obj)
    (check-equal? (obj 'a) 1)
    (check-equal? (obj 'b) 2)
    (check-equal? (obj 'c) 3)
    (define obj2 (obj 'a #:-> 5))
    (check-equal? (obj2 'a) 5)
    )
  (test-case "object-ref* and object-set*"
    (define obj
      (object [ball
               (object [position (object [x 1] [y 2])]
                       [velocity (object [x 3] [y 4])])]))
    (check-equal? (obj 'ball 'position 'x) 1)
    (check-equal? (obj 'ball 'position 'y) 2)
    (check-equal? (obj 'ball 'velocity 'x) 3)
    (check-equal? (obj 'ball 'velocity 'y) 4)
    (define obj2 (obj 'ball 'velocity 'x #:-> 5))
    (check-equal? (obj2 'ball 'position 'x) 1)
    (check-equal? (obj2 'ball 'position 'y) 2)
    (check-equal? (obj2 'ball 'velocity 'x) 5)
    (check-equal? (obj2 'ball 'velocity 'y) 4)
    )
  (test-case "methods, with immutable public fields and functional update"
    (define (make-fish sz)
      (object [size sz]
              [get-size (λ () size)]
              [grow (λ (amt)
                      (this 'size #:-> (+ amt size)))]
              [eat (λ (other-fish)
                     (grow (send other-fish 'get-size)))]))
    (define charlie (make-fish 10))
    (check-equal? (charlie 'size) 10)
    (define charlie2 (send charlie 'grow 6))
    (check-equal? (charlie2 'size) 16)
    (check-equal? (send charlie2 'get-size) 16)
    (check-equal? (send charlie 'get-size) 10)
    (define (make-hungry-fish sz)
      (object-extend (make-fish sz)
                     #:inherit (eat)
                     [eat-more (λ (fish1 fish2)
                                 (eat fish1)
                                 (eat fish2))]))
    (check-equal? (send (make-hungry-fish 32) 'get-size) 32)
    (define (make-picky-fish sz)
      (object-extend (make-fish sz)
                     #:super ([super-grow grow])
                     [grow (λ (amt)
                             (super-grow (* 3/4 amt)))]))
    (define daisy (make-picky-fish 20))
    (define daisy2 (send daisy 'eat charlie2))
    (check-equal? (send daisy2 'get-size) 32)
    )
  (test-case "methods, with mutable private fields"
    (define (make-fish sz)
      (define size sz)
      (object [get-size (λ () size)]
              [grow (λ (amt)
                      (set! size (+ amt size)))]
              [eat (λ (other-fish)
                     (grow (send other-fish 'get-size)))]))
    (define charlie (make-fish 10))
    (check-equal? (send charlie 'get-size) 10)
    (send charlie 'grow 6)
    (check-equal? (send charlie 'get-size) 16)
    (define (make-hungry-fish sz)
      (object-extend (make-fish sz)
                     #:inherit (eat)
                     [eat-more (λ (fish1 fish2)
                                 (eat fish1)
                                 (eat fish2))]))
    (check-equal? (send (make-hungry-fish 32) 'get-size) 32)
    (define (make-picky-fish sz)
      (object-extend (make-fish sz)
                     #:super ([super-grow grow])
                     [grow (λ (amt)
                             (super-grow (* 3/4 amt)))]))
    (define daisy (make-picky-fish 20))
    (send daisy 'eat charlie)
    (check-equal? (send daisy 'get-size) 32)
    )
  )
