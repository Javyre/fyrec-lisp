(defpackage fyrec-test
  (:use :cl
        :fyrec
        :parachute))
(in-package :fyrec-test)

;; NOTE: To run this test file, execute `(asdf:test-system :fyrec)' in your Lisp.

(define-test dummy
  (false nil)
  (true t))

