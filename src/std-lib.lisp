(in-package :fyrec)

(defun stdlib-compile-header (s)
  ; (format s "~&@std.I32    = type i32")
  ; (format s "~&@std.Int    = type @std.I32")
  (format s "~&%std.String = type { i32, i8* }"))

#|
(defgeneric stdlib-compile-defun (s) )
(defmacro stdlib-fyrec-defun ()
  `(defmethod ))


(stdlib-fyrec-defun "print()"
|#
