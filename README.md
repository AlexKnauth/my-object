my-object [![Build Status](https://travis-ci.org/AlexKnauth/my-object.png?branch=master)](https://travis-ci.org/AlexKnauth/my-object)
===

documentation: http://pkg-build.racket-lang.org/doc/my-object/index.html

my version of objects, inspired by "things" from https://github.com/jarcane/heresy

This is based on the examples from http://docs.racket-lang.org/guide/define-struct.html

Examples:
```racket
> (require my-object)
> (define p (object [x 1] [y 2]))
> p
(object [x 1] [y 2])
> (object? p)
#t
> (p 'x) ; by the way, you can use #'x here instead of 'x
1
> (p 'y)
2
> (define p2 (p 'x #:-> 3))
> p2
(object [x 3] [y 2])
> (define (posn x0 y0)
    (object [x x0] [y y0]
            [add (λ (p) (posn (+ x (p 'x)) (+ y (p 'y))))]
            [->list (λ () (list x y))]))
> (define p3 (send (posn 1 2) add (posn 3 4)))
> (send p3 ->list)
'(4 6)
> (define p3 (posn 1 2))
> (define p4 (object-extend p3 [x 3])) ; or (p3 'x #:-> 3)
> (send p4 ->list)
'(3 2)
> (define (3d-posn x0 y0 z0)
    (object-extend (posn x0 y0)
                   #:inherit (x y)
                   [z z0]
                   [add (λ (p) (3d-posn (+ x (p 'x))  (+ y (p 'y)) (+ z (p 'z))))]
                   [->list (λ () (list x y z))]))
> (3d-posn 1 2 3)
(object [x 1] [y 2] [add #<procedure>] [->list #<procedure>] [z 3])
```

