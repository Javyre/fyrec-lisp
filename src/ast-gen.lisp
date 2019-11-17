(in-package :fyrec)

;;=============================================================================

#|
b[x] = x;
main() = {
    a = 1;
    foo = Foo(1, 3);
    bar = Bar(
        a: 1,
        b: 2
    );

    c = vec!(1, 2, 3);
    d = arr!(1, 2, 3);
    for i in range(0, 3): {
        *(d+i);
        d[1]
    };

    c.0;
    get(c, 1);
    print('hi');
    b(0)
};
|#


;;=============================================================================

; (defparameter *pprint-ast-cur-indent* 0)
; (defparameter *pprint-ast-indent-step* "    ")
; (defmacro indent (form)
;   `(let ((*pprint-ast-cur-indent* (1+ *pprint-ast-cur-indent*)))
;      (indent/impl ,form)))
; (defun indent/impl (str)
;   (loop ))

#+nil
(pprint-ast t (parse "a(b, c) = { e = c(); b(e, d); 1};" (=fundef)))

(defgeneric pprint-ast (stream node &rest r))

(defmethod pprint-ast (s (node fundef) &rest r)
  (declare (ignore r))
  (format s "~A(~{~A~^, ~}) = "
          (fundef-name node)
          (fundef-args node))
  (pprint-ast s (fundef-body node))
  (princ ";" s))

(defmethod pprint-ast (s (node varlet) &rest r)
  (declare (ignore r))
  (format s "~A = " (varlet-name node))
  (pprint-ast s (varlet-val node)))

(defmethod pprint-ast (s (node eblock) &rest r)
  (declare (ignore r))
  (format s "~@<{~;~_~
             ~{~/fyrec.ast-gen:pprint-ast/;~_~}~
             ~/fyrec.ast-gen:pprint-ast/~_~
             ~;}~:>"
          (eblock-stmts node)
          (eblock-expr  node)))
(defmethod pprint-ast (s (node varref) &rest r)
  (declare (ignore r))
  (format s "~A" (varref-name node)))
(defmethod pprint-ast (s (node funcal) &rest r)
  (declare (ignore r))
  (format s "~A(~{~/fyrec.ast-gen:pprint-ast/~^, ~})"
          (funcal-name node)
          (funcal-args node)))
(defmethod pprint-ast (s (node litera) &rest r)
  (declare (ignore r))
  (format s "~A" (litera-val node)))

;;=============================================================================

#|
;;=============================================================================

#+nil
(parse-with-err "hello (9a)" (=toplvl))

#+nil
(parse "hello 9(a), b, c)" (%reraise-perror (=toplvl)))

#+nil
(time (parse "test" #.(=subseq (%any (?satisfies (lambda (c) (member c '(#\e #\s #\t))))))))

|#

(defmacro defparse (name &body body)
  (let ((impl-id (intern (concatenate
                           'string
                           (symbol-name name) "/IMPL"))))

    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (let ((,impl-id ,@body))
         (defun ,name () ,impl-id)))))

(defparse =ws
  (%any (=satisfies (c) (member c '(#\space #\newline #\tab)))))

(defmacro %tok (parser)
  `(%destruc (%list (=ws) ,parser)
             (_ r) r))

(defmacro %get-tok-pos (name &body parser)
  `(%tok (%get-pos ,name ,@parser)))

(defmacro =char-tok (chr)
  (let ((chr (if (stringp chr)
                 (progn (assert (= 1 (length chr)))
                        (aref chr 0))
                 chr)))

    `(%named-tok ,(format nil "'~A'" chr)
       (=satisfies (c)
         (char= c ,chr)))))

(defmacro =string-tok (str)
  `(%named-tok ,(format nil "\"~A\"" str)
     (=string ,str)))

(defmacro %named-tok (name &body parser)
  (assert (= 1 (length parser)))
  `(%tok (%named ,name ,@parser)))

(defmacro %surround (lhd parser rhd)
  `(%destruc (%list ,lhd ,parser ,rhd)
             (_ v _) v))

(defmacro %parens (parser)
  `(%surround (=char-tok "(") ,parser (=char-tok ")")))

(defmacro %braces (parser)
  `(%surround (=char-tok "{") ,parser (=char-tok "}")))

(defmacro %any-sep-by (delim parser)
  `(%destruc (%list (%any (%destruc (%list ,parser ,delim)
                                    (r _) r))
                    (%maybe ,parser))
             (els el) (append els (when el (list el)))))

(defparse =ident
  (%named-tok "ident"
    (%subseq (%list
               (=satisfies (c)
                 (or (lower-case-p c)
                     (member c '(#\_))))
               (%any (=satisfies (c)
                       (or (lower-case-p c)
                           (digit-char-p c)
                           (member c '(#\_)))))))))

(defparse =integer-lit
  (%named-tok "integer"
    (%map (%subseq (%some (=satisfies (c) (digit-char-p c))))
          (str) (parse-integer str))))

(defparse =string-lit
  (%named-tok "string"
    (%destruc (%list (=string "\"")
                     (%subseq (%any (%or (=satisfies (c)
                                           (not (member c '(#\" #\\))))
                                         (=string "\\\"")
                                         (=string "\\\\"))))
                     (=string "\""))
              (_ s _) s)))

;;=============================================================================

(defparse =module
  (%destruc (%list (%any (%destruc (%list (=toplvl) (=char-tok ";"))
                                   (tl _) tl))
                   (%named-tok "EOF" (=eof)))
            (tls _)
            (make-module :toplvls tls)))

(defparse =toplvl
  (%or (=fundef)))

(defparse =fundef
  (%get-tok-pos pos
    (%destruc (%list
                (=ident) (%parens (%any-sep-by (=char-tok ",") (=ident)))
                (=char-tok "=") (=expr))
              (id args _ val)
              (make-fundef :name id
                           :args args
                           :body val
                           :src-pos pos))))

(defparse =funcal
  (%get-tok-pos pos
    (%destruc (%list
                (=ident) (%parens (%any-sep-by (=char-tok ",") (=expr))))
              (id args)
              (make-funcal :name id
                           :args args
                           :src-pos pos))))

(defparse =litera
  (%get-tok-pos pos
    (%or (%map (=integer-lit) (v) (make-litera :vty :integer :val v :src-pos pos))
         (%map (=string-lit)  (v) (make-litera :vty :string  :val v :src-pos pos)))))

(defparse =eblock
  (%get-tok-pos pos
    (%braces (%destruc (%list (%any (%destruc (%list (%or (=varlet)
                                                          (=expr))
                                                     (=char-tok ";"))
                                              (e _) e))
                              (=expr))
                       (stmts expr)
                       (make-eblock :stmts stmts
                                    :expr expr
                                    :src-pos pos)))))

(defparse =varlet
  (%get-tok-pos pos
    (%destruc (%list (=ident) (=char-tok "=") (=expr))
              (name _ val)
              (make-varlet :name name
                           :val val
                           :src-pos pos))))

(defparse =varref
  (%get-tok-pos pos
    (%map (=ident)
          (name)
          (make-varref :name name :src-pos pos))))

(defparse =expr
  (%or (=eblock)
       (=funcal)
       (=litera)
       (=varref)))

(defun parse-module (prg)
  (parse prg (=module)))

#+nil
(parse "hello(abc) = abc(a({ a = b; 1 }));" #.(=fundef))


