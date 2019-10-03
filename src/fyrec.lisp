(defpackage fyrec
  (:use :cl :alexandria :let-plus :trivia :fyrec.parser))
(in-package :fyrec)
(setf *arity-check-by-test-call* nil)

