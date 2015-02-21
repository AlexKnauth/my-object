#lang afl racket/base

(provide object
         object?
         object-extend
         object-fields
         object-ref1   object-ref
         object-set-m1 object-set-m
         object-set1   object-set
         send dynamic-send
         send* send+
         this
         )

(require racket/promise
         racket/match
         racket/list
         racket/local
         racket/function
         racket/sequence
         generic-bind
         keyword-lambda/keyword-case-lambda
         kw-utils/keyword-lambda
         syntax/parse/define
         syntax/stx
         unstable/sequence
         unstable/hash
         racket/stxparam
         racket/dict
         my-format
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
               object-field-promises
               object-fields-promise
               λfield
               λfield-final?)
  (defs-renamed ([obj object] [λfld λfield])
    (define object
      (keyword-lambda (kws kw-args ths . rst)
        (keyword-apply object-proc kws kw-args ths rst)))
    (define (λfield λfld ths)
      (λfield-proc λfld ths)))
  (struct object (name λfields field-promises fields-promise)
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
     (define (dict-iterate-first obj)     (object-iterate-first obj))
     (define (dict-iterate-next obj pos)  (object-iterate-next obj))
     (define (dict-iterate-key obj pos)   (object-iterate-key obj))
     (define (dict-iterate-value obj pos) (object-iterate-value obj))
     (define (dict-map obj proc)          (object-dict-map obj))
     (define (dict-for-each obj proc)     (object-for-each obj))
     (define (dict-empty? obj)            (empty? (object-field-promises obj)))
     (define (dict-count obj)             (length (object-field-promises obj)))
     (define (dict-keys obj)              (map car (object-field-promises obj)))
     (define (dict-values obj)            (map cdr (object-fields obj)))
     (define (dict->list obj)             (object-fields obj))
     (define (in-dict obj)                (in-pairs (object-fields obj)))
     (define (in-dict-keys obj)           (in-list (map car (object-field-promises obj))))
     (define (in-dict-values obj)         (in-list (map cdr (object-field-promises obj))))
     (define (in-dict-pairs obj)          (in-list (object-fields obj)))]
    )
  (struct λfield (stx λaugmentable λoverrideable final?) #:transparent
    #:property prop:procedure λfld)
  )

(define empty-fields-promise (delay '()))
(void (force empty-fields-promise))

(define empty-object (-object 'empty-object '() '() empty-fields-promise))

(define (default-λaugmentable ths #:augment-with inner)
  inner)

(define (default-λoverrideable ths)
  void)

(define default-λfield
  (λfield #f default-λaugmentable default-λoverrideable #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; macros

(define-syntax-parameter this #f)

(define-syntax-parser deffld
  [(deffld [id1:id id2:id] ths:id)
   #'(def-var-like-trans id1 #'(object-ref1 ths #'id2))]
  [(deffld id:id ths:id)
   #'(deffld [id id] ths)])

(begin-for-syntax
  (define-splicing-syntax-class maybe-inherit/super
    [pattern (~seq (~or (~optional (~seq #:inherit (inherit-id:id ...))
                                   #:defaults ([(inherit-id 1) '()]))
                        (~optional (~seq #:super ([super-id1:id super-id2:id] ...))
                                   #:defaults ([(super-id1 1) '()] [(super-id2 1) '()])))
                   ...)])
  (define-splicing-syntax-class field-decls
    [pattern (~and (~seq field-decl ...)
                   (~seq (~or [normal-field:id normal-field-expr:expr]
                              [final-field:id final-field-expr:expr #:final]
                              [augmentable-field:id augmentable-field-expr:expr
                                                    #:augmentable #:with inner-id:id])
                         ...))
             #:with ([field field-expr field-args] ...)
             #'([normal-field normal-field-expr (ths)] ...
                [final-field final-field-expr (ths)] ...
                [augmentable-field augmentable-field-expr
                                   (ths #:augment-with inner-id)] ...
                )]))

(define-syntax-parser object
  [(object :field-decls)
   #'(object-extend empty-object field-decl ...)]
  [(object #:extends super-obj-expr:expr :maybe-inherit/super :field-decls)
   #'(object-extend super-obj-expr #:inherit (inherit-id ...) #:super ([super-id1 super-id2] ...)
                    field-decl ...)])

(define-simple-macro
  (object-extend super-obj-expr:expr :maybe-inherit/super :field-decls)
  (local [(define super super-obj-expr)
          (match-define
            (-object _ super.λfields _ _)
            super)
          (define (field . field-args)
            (syntax-parameterize ([this (make-rename-transformer #'ths)])
              (deffld inherit-id ths) ...
              (define super-id1
                ((dict-ref super.λfields 'super-id2) ths))
              ...
              (deffld field ths) ...
              field-expr))
          ...]
    (extend-object
     super
     (list (cons #'field field) ...)
     #:final '(final-field ...))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions

(define (extend-object super new-procs #:final new-final-fields)
  (match-define
    (-object _ super.λfields _ _)
    super)
  (define super.final-fields (object-final-fields super))
  (for ([p (in-list new-procs)])
    (match-define (cons k v) p)
    (when (member (stx-e k) super.final-fields)
      (raise-final-field-error k super)))
  (λfields->object
   (extend-λfields super.λfields new-procs
                   #:final new-final-fields)))

(define (λfields->object λfields)
  (define fld-promises
    (for/list ([p (in-list λfields)])
      (match-define (cons k v) p)
      (cons k (delay (v ths)))))
  (define flds-promise
    (delay (for/list ([p (in-list fld-promises)])
             (match-define (cons k v) p)
             (cons k (force v)))))
  (define ths
    (-object #f λfields fld-promises flds-promise))
  (force flds-promise)
  ths)

(define (augment/override-λfield λfld proc #:stx [stx #f] #:final? final?)
  (define-values (req-kws all-kws) (procedure-keywords proc))
  (match-define (λfield old-stx λaugmentable λoverrideable super-final?) λfld)
  (when super-final?
    (raise-final-field-error (cond [(syntax? stx) stx] [(syntax? old-stx) old-stx]
                                   [stx stx] [old-stx old-stx] [else (object-name proc)])
                             #f))
  (match* (req-kws all-kws)
    [('() '())
     (λfield (if (syntax? stx) stx old-stx)
             λaugmentable proc final?)]
    [('(#:augment-with) '(#:augment-with))
     (λfield (if (syntax? stx) stx old-stx)
             (λ (ths #:augment-with inner-inner)
               (define inner (proc ths #:augment-with inner-inner))
               (λaugmentable ths #:augment-with inner))
             default-λoverrideable final?)]
    ))
  
(define (λfield-proc λfld ths)
  (match-define (λfield stx λaugmentable λoverrideable final?) λfld)
  (λaugmentable ths #:augment-with (λoverrideable ths)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define (object-final-fields obj)
  (for/list ([(k v) (in-pairs (object-λfields obj))]
             #:when (λfield-final? v))
    k))

(define (object-has-field? obj fld)
  (dict-has-key? (object-field-promises obj) (stx-e fld)))

(define (object-ref1 obj fld #:else [failure (λ () (object-ref-failure obj fld))])
  (force (dict-ref (object-field-promises obj) (stx-e fld) failure)))

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
  (extend-object obj (list (cons fld m)) #:final '()))

(define (object-set1 obj fld #:-> v)
  (object-set-m1 obj fld #:->m (procedure-rename (λ (ths) v) (stx-e fld))))

(define (object-set-m obj #:->m m fld . flds)
  (match (cons fld flds)
    [(list fld) (object-set-m1 obj fld #:->m m)]
    [(cons fld rst)
     (define obj.fld (object-ref1 obj fld))
     (define new-obj.fld (apply object-set-m obj.fld #:->m m rst))
     (object-set1 obj fld #:-> new-obj.fld)]))

(define (object-set obj #:-> v fld . flds)
  (apply object-set-m obj #:->m (procedure-rename (λ (ths) v) (stx-e (last (cons fld flds))))
         fld flds))

(define (dynamic-send obj method . args)
  (apply (object-ref1 obj method #:else (λ () (send-failure obj method))) args))

(define-syntax send
  (syntax-parser
    [(send obj method:id . args)
     #'(dynamic-send obj #'method . args)]
    [(send obj ((~or (~literal quote) (~literal syntax)) method:id) . args)
     #'(dynamic-send obj #'method . args)]
    [(send obj ((~literal identity) method:expr) . args)
     #'(dynamic-send obj method . args)]
    [(send obj . field:id)
     #'(object-ref obj #'field)]
    [send:id #'dynamic-send]))

(define-simple-macro (send* obj-expr:expr msg:expr ...+)
  (let ([obj obj-expr])
    (send obj . msg)
    ...))

(define-simple-macro (send+ obj-expr:expr msg:expr ...)
  (let* ([obj obj-expr]
         [obj (send* obj msg)] ...)
    obj))


(define (extend-λfields λfields alst #:final final-fields)
  (define-values (i->p len)
    (for/fold ([i->p '()] [len (length λfields)])
              ([p (in-list alst)])
      (define k (stx-e (car p)))
      (define i
        (for/or ([λfld-p (in-list λfields)] [i (in-naturals)])
          (and (equal? (car λfld-p) k) i)))
      (cond [i    (values (cons (cons i p) i->p) len)]
            [else (values (cons (cons len p) i->p) (add1 len))])))
  (for/list ([i (in-range len)]
             [p (in-sequence-forever λfields (cons #f default-λfield))])
    (match (dict-ref i->p i #f)
      [#f p]
      [(cons k-stx new-v)
       (match-define (cons _ old-v) p)
       (define k (stx-e k-stx))
       (cons k
             (augment/override-λfield
              old-v new-v #:stx (if (syntax? k-stx) k-stx #f)
              #:final? (member k final-fields)))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (object-iterate-first obj)
  (if (empty? (object-field-promises))
      #f
      0))

(define (object-iterate-next obj i)
  (if (< (add1 i) (length (object-field-promises obj)))
      (add1 i)
      #f))

(define (object-iterate-key obj i)
  (car (list-ref (object-field-promises obj) i)))

(define (object-iterate-value obj i)
  (force (cdr (list-ref (object-field-promises obj) i))))

(define (object-dict-map obj proc)
  (for/list ([p (in-list (object-field-promises obj))])
    (proc (car p) (cdr p))))

(define (object-for-each obj proc)
  (for ([p (in-list (object-field-promises obj))])
    (proc (car p) (cdr p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (obj-write-proc obj out mode)
  (match-define (-object name λfields field-promises fields-promise) obj)
  (match mode
    [0  (write-string "(object" out)
        (for ([(k λv) (in-pairs λfields)]
              [(k2 v) (in-pairs (force fields-promise))])
          (unless (eq? k k2) (error 'obj "this should never happen\n  k: ~v\n  k2: ~v\n" k k2))
          (cond [(λfield-final? λv)
                 (fprintf out " [~a ~v #:final]" k v)]
                [else
                 (fprintf out " [~a ~v]" k v)]))
        (write-string ")" out)
        (void)]
    [_ #:when (symbol? name) (fprintf out "#<object:~a>" name)]
    [_ (write-string "#<object" out)
       (for ([p (in-list (force fields-promise))])
         (match-define (cons k v) p)
         (fprintf out " [~a ~v]" k v))
       (write-string ">" out)
       (void)]))

(define (object-ref-failure obj fld)
  (define fld-stx (stx fld))
  (raise-syntax-error 'object-ref
                      (-format "object does not have field" "\n"
                               "  field: ~a" (syntax-e fld-stx) "\n"
                               "  object: ~v" obj)
                      fld-stx))

(define (object-ref*-failure obj flds)
  (define fld-stxs (stx-map stx flds))
  (define fld-stx
    (let loop ([obj obj] [flds fld-stxs])
      (match flds
        [(list) (error 'object-ref*-failure "this should never happen")]
        [(list-rest fst rst)
         (cond [(object-has-field? obj fst) (loop (object-ref obj fst) rst)]
               [else fst])])))
  (raise-syntax-error 'object-ref*
                      (-format
                       "object does not have nested field chain" "\n"
                       "  field chain: ~a" (map syntax-e fld-stxs) "\n"
                       "  object: ~v" obj)
                      fld-stx))

(define (send-failure obj method)
  (define method-stx (stx method))
  (raise-syntax-error 'send
                      (-format
                       "object does not have method" "\n"
                       "  method: ~a" (syntax-e method-stx) "\n"
                       "  object: ~v" obj)
                      method-stx))

(define (raise-final-field-error field super)
  (define field-stx (stx field))
  (raise-syntax-error 'object-extend
                      (if super
                          (format "cannot override the field ~a of ~v" (syntax-e field-stx) super)
                          (format "cannot override the field ~a" (syntax-e field-stx)))
                      field-stx))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test-case "simple"
    (define obj
      (object [a 1] [b 2] [c 3]))
    (check-pred object? obj)
    (check-equal? (obj #'a) 1)
    (check-equal? (obj 'b) 2)
    (check-equal? (obj 'c) 3)
    (define obj2 (obj 'a #:-> 5))
    (check-equal? (obj2 'a) 5)
    (check-equal? (send obj2 . a) 5)
    (check-equal? (send+ obj2 a) 5)
    )
  (test-case "object-ref* and object-set*"
    (define obj
      (object [ball
               (object [position (object [x 1] [y 2])]
                       [velocity (object [x 3] [y 4])])]))
    (check-equal? (obj #'ball #'position #'x) 1)
    (check-equal? (obj 'ball 'position 'y) 2)
    (check-equal? (obj 'ball 'velocity 'x) 3)
    (check-equal? (obj 'ball 'velocity 'y) 4)
    (define obj2 (obj #'ball 'velocity 'x #:-> 5))
    (check-equal? (obj2 #'ball #'position #'x) 1)
    (check-equal? (obj2 'ball 'position 'y) 2)
    (check-equal? (obj2 'ball 'velocity 'x) 5)
    (check-equal? (obj2 'ball 'velocity 'y) 4)
    (check-equal? (send+ obj2 ball velocity y) 4)
    )
  (test-case "methods, with immutable public fields and functional update"
    (define (make-fish sz)
      (object [size sz]
              [get-size (λ () size)]
              [grow (λ (amt)
                      (this 'size #:-> (+ amt size)))]
              [eat (λ (other-fish)
                     (grow (send other-fish get-size)))]))
    (define charlie (make-fish 10))
    (check-equal? (charlie 'size) 10)
    (define charlie2 (send charlie grow 6))
    (check-equal? (charlie2 'size) 16)
    (check-equal? (send charlie2 get-size) 16)
    (check-equal? (send charlie get-size) 10)
    (define (make-hungry-fish sz)
      (object-extend (make-fish sz)
                     #:inherit (eat)
                     [eat-more (λ (fish1 fish2)
                                 (send+ this (eat fish1) (eat fish2)))]))
    (define hungry-fish (make-hungry-fish 32))
    (check-equal? (hungry-fish 'size) 32)
    (check-equal? ((send hungry-fish eat-more charlie charlie2) 'size) 58)
    (define (make-picky-fish sz)
      (object-extend (make-fish sz)
                     #:super ([super-grow grow])
                     [grow (λ (amt)
                             (super-grow (* 3/4 amt)))]))
    (define daisy (make-picky-fish 20))
    (define daisy2 (send daisy eat charlie2))
    (check-equal? (send daisy2 get-size) 32)
    )
  (test-case "methods, with mutable private fields"
    (define (make-fish sz)
      (define size sz)
      (object [get-size (λ () size)]
              [grow (λ (amt)
                      (set! size (+ amt size)))]
              [eat (λ (other-fish)
                     (grow (send other-fish get-size)))]))
    (define charlie (make-fish 10))
    (check-equal? (send charlie get-size) 10)
    (send charlie grow 6)
    (check-equal? (send charlie get-size) 16)
    (define (make-hungry-fish sz)
      (object-extend (make-fish sz)
                     #:inherit (eat)
                     [eat-more (λ (fish1 fish2)
                                 (eat fish1)
                                 (eat fish2))]))
    (check-equal? (send (make-hungry-fish 32) get-size) 32)
    (define (make-picky-fish sz)
      (object-extend (make-fish sz)
                     #:super ([super-grow grow])
                     [grow (λ (amt)
                             (super-grow (* 3/4 amt)))]))
    (define daisy (make-picky-fish 20))
    (send daisy eat charlie)
    (check-equal? (send daisy get-size) 32)
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
    (check-equal? (send sub m3 1) 2))
  (test-case "final"
    (define sup
      (object [m1 (λ (x) x) #:final] [m2 (λ (x) x)]))
    (check-exn #rx"object-extend: cannot override the field m1"
               (λ () (object-extend sup [m1 (λ (x) (add1 x))])))
    (define sub
      (object-extend sup [m2 (λ (x) (add1 x)) #:final]))
    (check-exn #rx"object-extend: cannot override the field m2"
               (λ () (object-extend sub [m2 (λ (x) (add1 x))])))
    (check-exn #rx"object-extend: cannot override the field m1"
               (λ () (object-extend sub [m1 (λ (x) (add1 x))]))))
  (test-case "inner"
    (define sup
      (object [m1 (λ (x) (define r (inner x))
                    (if (integer? r) r (error 'm1 "needs to return an integer, given ~v" r)))
                  #:augmentable #:with inner]))
    (check-exn #rx"m1: needs to return an integer, given 'not-a-real-number"
               (λ () (send (object-extend sup [m1 (λ (x) 'not-a-real-number)]) m1 0)))
    (check-exn #rx"m1: needs to return an integer, given 1.5"
               (λ () (send (object-extend sup [m1 (λ (x) 1.5)]) m1 0)))
    (define sub2
      (object-extend sup [m1 (λ (x) 5)]))
    (check-equal? (send sub2 m1 0) 5)
    (define sub3
      (object-extend sub2 [m1 (λ (x) "also not a real number")]))
    (check-exn #rx"m1: needs to return an integer, given \"also not a real number\""
               (λ () (send sub3 m1 0)))
    (define sub4
      (object #:extends sup
              [m1 (λ (x) (define r (inner x))
                    (if (and (real? r) (positive? r))
                        r
                        (error 'm1 "needs to return a positive number, given ~v" r)))
                  #:augmentable #:with inner]))
    (define sub5
      (object-extend sub4 [m1 (λ (x) x)]))
    (check-equal? (send sub5 m1 3) 3)
    (check-exn #rx"m1: needs to return a positive number, given -1"
               (λ () (send sub5 m1 -1)))
    (check-exn #rx"m1: needs to return an integer, given 1.5"
               (λ () (send sub5 m1 1.5)))
    )
  (test-case "inner with fields"
    (define sup
      (object [a (cond [(integer? inner) inner]
                       [(eq? inner void) 0]
                       [else (error 'a "expected an integer, given ~v" inner)])
                 #:augmentable #:with inner]))
    (check-exn #rx"a: expected an integer, given 'not-a-real-number"
               (λ () (object-extend sup [a 'not-a-real-number])))
    (check-exn #rx"a: expected an integer, given 1.5"
               (λ () (object-extend sup [a 1.5])))
    (define sub2
      (object-extend sup [a 5]))
    (check-equal? (sub2 'a) 5)
    (check-exn #rx"a: expected an integer, given \"also not a real number\""
               (λ () (object-extend sub2 [a "also not a real number"])))
    (define sub4
      (object #:extends sup
              [a (cond [(and (real? inner) (positive? inner)) inner]
                       [(eq? inner void) 0]
                       [else (error 'a "expected a positive number, given ~v" inner)])
                 #:augmentable #:with inner]))
    (check-equal? ((object-extend sub4 [a 3]) 'a) 3)
    (check-exn #rx"a: expected a positive number, given -1"
               (λ () (object-extend sub4 [a -1])))
    (check-exn #rx"a: expected an integer, given 1.5"
               (λ () (object-extend sub4 [a 1.5])))
    )
  (test-case "referring to other fields within field expressions"
    (define obj
      (object [x 1]
              [y (add1 x)]
              [ths this]))
    (check-equal? (obj 'x) 1)
    (check-equal? (obj 'y) 2)
    (check-equal? (obj 'ths) obj)
    )
  (test-case "order of fields"
    (define obj
      (object [first 1]
              [second 2]
              [third 3]
              [fourth 4]))
    (check-equal? (object-fields obj)
                  '([first . 1] [second . 2] [third . 3] [fourth . 4]))
    (define obj2
      (object-extend obj [third "3"] [fifth 5] [second "2"]))
    (check-equal? (object-fields obj2)
                  '([first . 1] [second . "2"] [third . "3"] [fourth . 4] [fifth . 5]))
    (check-equal? (format "~v" obj2)
                  "(object [first 1] [second \"2\"] [third \"3\"] [fourth 4] [fifth 5])")
    (define out3 (open-output-string))
    (define obj3
      (parameterize ([current-output-port out3])
        (object [first (displayln "first")]
                [second (begin (displayln "second")
                               third
                               (displayln "fourth"))]
                [fifth (displayln "fifth")]
                [third (displayln "third")] ; because it is referenced by second
                [sixth (displayln "sixth")])))
    (check-equal? (get-output-string out3)
                  "first\nsecond\nthird\nfourth\nfifth\nsixth\n")
    (define out4 (open-output-string))
    (define obj4
      (parameterize ([current-output-port out4])
        (object #:extends obj3
                [third (displayln "3rd")]
                [seventh (displayln "7th")])))
    (check-equal? (get-output-string out4)
                  "first\nsecond\n3rd\nfourth\nfifth\nsixth\n7th\n")
    )
  )
