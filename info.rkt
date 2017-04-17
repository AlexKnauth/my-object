#lang info

(define collection 'multi)

(define deps '(("base" #:version "6.2.900.6")
               "lens"
               "hash-lambda"
               "kw-utils"
               "unstable-lib"
               ))

(define build-deps '("rackunit-lib"
                     "scribble-lib"
                     "racket-doc"
                     "heresy"
                     ))

