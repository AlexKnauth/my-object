#lang racket/base

(provide object
         object?
         object-extend
         object-fields
         object-ref1   object-ref
         object-set-m1 object-set-m
         object-set1   object-set
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
         racket/dict
         "stuff.rkt"
         (for-syntax racket/base
                     syntax/parse
                     ))
(module+ test
  (require rackunit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; structs

(defs-renamed ([-object object]
               object?
               object-λfields
               object-fields-promise)
  (defs-renamed ([obj object])
    (define object
      (keyword-lambda (kws kw-args ths . rst)
        (keyword-apply object-proc kws kw-args ths rst))))
  (struct object (name λfields fields-promise)
    #:property prop:procedure obj
    #:methods gen:custom-write
    [(define (write-proc obj out mode)
       (obj-write-proc obj out mode))]
    #:methods gen:dict
    [(define (dict-ref obj key [failure (λ () (object-ref-failure obj key))])
       (object-ref1 obj key #:else failure))
     (define (dict-set obj k v)
       (object-set1 obj k v))
     (define (dict-has-key? obj key)
       (object-has-field? obj key))
     (define (dict-iterate-first obj)     (hash-iterate-first (object-fields obj)))
     (define (dict-iterate-next obj pos)  (hash-iterate-next (object-fields obj) pos))
     (define (dict-iterate-key obj pos)   (hash-iterate-key (object-fields obj) pos))
     (define (dict-iterate-value obj pos) (hash-iterate-value (object-fields obj) pos))
     (define (dict-map obj proc)          (hash-map (object-fields obj) proc))
     (define (dict-for-each obj proc)     (hash-for-each (object-fields obj) proc))
     (define (dict-empty? obj)            (hash-empty? (object-fields obj)))
     (define (dict-count obj)             (hash-count (object-fields obj)))
     (define (dict-keys obj)              (hash-keys (object-fields obj)))
     (define (dict-values obj)            (hash-values (object-fields obj)))
     (define (dict->list obj)             (hash->list (object-fields obj)))
     (define (in-dict obj)                (in-hash (object-fields obj)))
     (define (in-dict-keys obj)           (in-hash-keys (object-fields obj)))
     (define (in-dict-values obj)         (in-hash-values (object-fields obj)))
     (define (in-dict-pairs obj)          (in-hash-pairs (object-fields obj)))]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; macros

(define-syntax-parameter this #f)

(define-syntax-parser deffld
  [(deffld [id1:id id2:id] ths:id)
   #'(def-var-like-trans id1 #'(object-ref1 ths 'id2))]
  [(deffld id:id ths:id)
   #'(deffld [id id] ths)])

(begin-for-syntax
  (define-splicing-syntax-class maybe-inherit/super
    [pattern (~seq (~or (~optional (~seq #:inherit (inherit-id:id ...))
                                   #:defaults ([(inherit-id 1) '()]))
                        (~optional (~seq #:super ([super-id1:id super-id2:id] ...))
                                   #:defaults ([(super-id1 1) '()] [(super-id2 1) '()])))
                   ...)]))

(define-syntax-parser object
  [(object [field:id expr:expr] ...)
   #'(local [(define (field ths)
               (syntax-parameterize ([this (make-rename-transformer #'ths)])
                 (deffld field ths) ...
                 expr))
             ...]
       (λfields->object (make-immutable-hasheq (list (cons 'field field) ...))))]
  [(object #:extends super-obj-expr:expr :maybe-inherit/super [field:id expr:id] ...)
   #'(object-extend super-obj-expr #:inherit (inherit-id ...) #:super ([super-id1 super-id2] ...)
                    [field expr] ...)])

(define-simple-macro
  (object-extend super-obj-expr:expr :maybe-inherit/super [field:id expr:expr] ...)
  (local [(define super super-obj-expr)
          (define super.λfields (object-λfields super))
          (define (field ths)
            (syntax-parameterize ([this (make-rename-transformer #'ths)])
              (deffld inherit-id ths) ...
              (define super-id1
                ((hash-ref super.λfields 'super-id2) ths))
              ...
              (deffld field ths) ...
              expr))
          ...]
    (λfields->object
     (extend-λfields super.λfields (make-immutable-hasheq (list (cons 'field field) ...))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions

(define (λfields->object λfields)
  (define flds-promise
    (delay (for/hash ([(k v) (in-hash λfields)])
             (values k (v ths)))))
  (define ths
    (-object #f λfields flds-promise))
  (force flds-promise)
  ths)

(define object-proc
  (keyword-case-lambda
   [(obj #:fields _) (object-fields obj)]
   [(obj fld #:else [failure (λ()(object-ref-failure obj fld))]) (object-ref1 obj fld #:else failure)]
   [(obj fld #:-> v) (object-set1 obj fld #:-> v)]
   [(obj fld #:->m m) (object-set-m1 obj fld #:->m m)]
   [(obj #:else [failure fail-sym] . flds) (apply object-ref obj flds #:else failure)]
   [(obj #:-> v fld . flds) (apply object-set obj #:-> v fld flds)]
   [(obj #:->m m fld . flds) (apply object-set-m obj #:->m m fld flds)]
   ))

(define (object-fields obj)
  (force (object-fields-promise obj)))

(define (object-has-field? obj fld)
  (hash-has-key? (object-fields obj) fld))

(define (object-ref1 obj fld #:else [failure (λ () (object-ref-failure obj fld))])
  (hash-ref (object-fields obj) fld failure))

(define fail-sym (gensym 'failure))
(define (object-ref obj #:else [failure fail-sym] . flds)
  (define fail (if (eq? failure fail-sym)
                   (λ () (object-ref*-failure obj flds))
                   failure))
  (match flds
    [(list) obj]
    [(cons fld flds)
     (if (object-has-field? obj fld)
         (apply object-ref (object-ref1 obj fld) flds #:else fail)
         (object-ref1 obj fld #:else fail))]))

(define (object-set-m1 obj fld #:->m m)
  (define λfields (object-λfields obj))
  (define new-λfields (extend-λfields λfields (hasheq fld m)))
  (λfields->object new-λfields))

(define (object-set1 obj fld #:-> v)
  (object-set-m1 obj fld #:->m (λ (ths) v)))

(define (object-set-m obj #:->m m fld . flds)
  (match (cons fld flds)
    [(list fld) (object-set-m1 obj fld #:->m m)]
    [(cons fld rst)
     (define obj.fld (object-ref1 obj fld))
     (define new-obj.fld (apply object-set-m obj.fld #:->m m rst))
     (object-set1 obj fld #:-> new-obj.fld)]))

(define (object-set obj #:-> v fld . flds)
  (apply object-set-m obj #:->m (λ (ths) v) fld flds))

(define (send obj method . args)
  (apply (object-ref1 obj method #:else (λ () (send-failure obj method))) args))

(define-simple-macro (send* obj-expr:expr (method:id arg ...) ...+)
  (let ([obj obj-expr])
    (send obj 'method arg ...)
    ...))

(define-simple-macro (send+ obj-expr:expr msg:expr ...)
  (let* ([obj obj-expr]
         [obj (send* obj msg)] ...)
    obj))
  

(define (extend-λfields λfields hsh)
  (hash-union λfields hsh #:combine (λ (v1 v2) v2)))

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

(define (object-ref-failure obj fld)
  (error 'object-ref
         (string-append
          "object does not have field" "\n"
          "  field: ~a" "\n"
          "  object: ~v")
         fld obj))

(define (object-ref*-failure obj flds)
  (error 'object-ref*
         (string-append
          "object does not have nested field chain" "\n"
          "  field chain: ~a" "\n"
          "  object: ~v")
         flds obj))

(define (send-failure obj method)
  (error 'send
         (string-append
          "object does not have method" "\n"
          "  method: ~a" "\n"
          "  object: ~v")
         method obj))

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
                                 (send+ this (eat fish1) (eat fish2)))]))
    (define hungry-fish (make-hungry-fish 32))
    (check-equal? (hungry-fish 'size) 32)
    (check-equal? ((send hungry-fish 'eat-more charlie charlie2) 'size) 58)
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
  (test-case "test super corner-case"
    (define sup
      (object [m1 (λ (x) (error 'nevergetshere))]
              [m2 (λ (y) (m1 y))]))
    (define sub
      (object-extend sup
                     #:super ([super-m2 m2])
                     [m1 (λ (x) (add1 x))]
                     [m2 (λ (y) (error 'nevergetshere))]
                     [m3 (λ (y) (super-m2 y))]))
    (check-equal? (send sub 'm3 1) 2))
  )
