#lang scribble/manual

@(require scribble/eval
          (for-label my-object racket/base racket/contract))

@title{my-object}

@defmodule[my-object]{
my version of objects, inspired by
@secref["Things" #:doc '(lib "heresy/doc/heresy.scrbl")] from
@racketmodname[heresy]

Also, the objects here do not mean @racketmodname[racket/class] objects.
}

@section{Forms and Functions}

@defform[(object [field-id expr] ...)]{
creates and returns an object with the @racket[field-id]s mapped to the
@racket[expr]s.  Each @racket[expr] can refer to @racket[this] and all the other
@racket[field-id]s.  

See also @racket[object-extend].  

If an @racket[expr] is a function, then that function can be used as a method
for the object, but methods are not treated specially; they are just normal
fields that happen to have functions stored in them.  

Each @racket[field-id] is public and immutable.  Private mutable fields are also
possible (see @secref["fish-mutable"]).}

@defform[(object-extend obj option ... [field-id expr] ...)
         #:grammar ([option (code:line #:inherit (inherit-id ...))
                            (code:line #:super ([super-id1 super-id2] ...))])]{
similar to both @racket[struct-copy] and object inheritance.  

If the @racket[#:inherit] option is provided, the @racket[inherit-id]s are
available as bindings within the @racket[expr]s.

If the @racket[#:super] option is provided, the @racket[super-id1]s are
available within the @racket[expr]s, and a @racket[super-id1] refers to the @racket[super-id2]
field of the super object.  
}

@defproc[(object? [v any/c]) boolean?]{
returns @racket[#t] if @racket[v] is an object, @racket[#f] otherwise.
}

@defproc[(object-fields [obj object?]) (hash/c symbol? any/c #:immutable #t)]{
returns a hash-table containing the fields of @racket[obj].
}

@defproc[(send [obj object?] [method symbol?] [arg any/c] ...) any]{
equivalent to @racket[((obj method) arg ...)].  
}

@defidform[this]{
within an @racket[object] or @racket[object-extend] form, refers to the current object.
}

@section{Examples}

@subsection{Posn example based on racket guide for structs}

This is based on the examples from
@secref["define-struct" #:doc '(lib "scribblings/guide/guide.scrbl")].

@examples[
  (require my-object)
  (define p (object [x 1] [y 2]))
  p
  (object? p)
  (p 'x)
  (p 'y)
  (define p2 (p 'x #:-> 3))
  p2
  (define (posn x0 y0)
    (object [x x0] [y y0]
            [add (λ (p) (posn (+ x (p 'x)) (+ y (p 'y))))]
            [->list (λ () (list x y))]))
  (define p3 (send (posn 1 2) 'add (posn 3 4)))
  (send p3 '->list)
  (define p3 (posn 1 2))
  (define p4 (object-extend p3 [x 3])) (code:comment "or (p3 'x #:-> 3)")
  (send p3 '->list)
  (define (3d-posn x0 y0 z0)
    (object-extend (posn x0 y0)
                   #:inherit (x y)
                   [z z0]
                   [add (λ (p) (3d-posn (+ x (p 'x))  (+ y (p 'y)) (+ z (p 'z))))]
                   [->list (λ () (list x y z))]))
  (3d-posn 1 2 3)
]

@subsection[#:tag "fish-mutable"]{Fish example based on racket guide for objects}

This is based on the examples from @secref["classes" #:doc '(lib "scribblings/guide/guide.scrbl")].

@examples[
  (require my-object)
  (define (make-fish sz)
    (define size sz) (code:comment "private mutable field")
    (object [get-size (λ () size)]
            [grow (λ (amt)
                    (set! size (+ amt size)))]
            [eat (λ (other-fish)
                   (grow (send other-fish 'get-size)))]))
  (define charlie (make-fish 10))
  (send charlie 'get-size)
  (send charlie 'grow 6)
  (send charlie 'get-size)
  (define (make-hungry-fish sz)
    (object-extend (make-fish sz)
                   #:inherit (eat)
                   [eat-more (λ (fish1 fish2)
                               (eat fish1)
                               (eat fish2))]))
  (send (make-hungry-fish 32) 'get-size)
  (define (make-picky-fish sz)
    (object-extend (make-fish sz)
                   #:super ([super-grow grow])
                   [grow (λ (amt)
                           (super-grow (* 3/4 amt)))]))
  (define daisy (make-picky-fish 20))
  (send daisy 'eat charlie)
  (send daisy 'get-size)
]


