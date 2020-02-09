(in-package :fyrec)

(defstruct comp-ctx prg module types)

(defun ctx-find-node-ty (id ctx)
  (or (cdr 
        (find-if (lambda-ematch ((cons (tvar :name (list :ast id0)) _)
                                 (equal id id0))
                                ((cons _ _) nil))
                 (comp-ctx-types ctx)))
      (error (format nil "type for ast node ~A not found" id))))

(defun ctx-find-func (id ctx)
  (find-if (lambda-ematch ((fundef name)
                           (equal name id)))
           (module-toplvls (comp-ctx-module ctx))))

(defparameter *local-var-count* 0)
(defun gen-local (&optional (name ""))
  (let ((c *local-var-count*))
    (incf *local-var-count*)
    (format nil "%~A~A" name c)))

(defun emit-val (s fmt &rest args)
  (let ((val (gen-local)))
    (format s "~&~A = " val)
    (apply #'format s fmt args)
    val))

(defun emit (s fmt &rest args)
  (fresh-line s)
  (apply #'format s fmt args))

;;=============================================================================

(defun compile-module (s ctx)
  (let* ((mainf (ctx-find-func "main" ctx))
         (rty   (make-type-t :name :integer))
         (fty   (make-type-t :name :fun 
                             :args (list rty))))

    (stdlib-compile-header s)
    (compile-fundef s mainf fty ctx)))

(defun compile-fundef (s f ty ctx)
  (ematch f
    ((fundef name args body id)
     (let-match* ((*local-var-count* 0)
                  (sty  (ctx-find-node-ty id ctx))
                  (fctx (instantiate-type sty ty ctx))

                  ((type-t :name :fun :args aty) ty)
                  (aty (reverse aty))
                  (rty (compile-type (pop aty) ctx))
                  (arg-vals (mapcar (lambda (ty a)
                                      (format nil "~A %~A.arg"
                                              (compile-type ty ctx) a))
                                    aty  
                                    args)))

       (format s "~&~%define ~A @~A(~{~A~^, ~}) {"
               rty name arg-vals)

       (format s "~&entry:")
       ; (incf *local-var-count*)

       (loop for a  in args
             for ty in aty do
             (let ((ty (compile-type ty ctx)))
               (format s "~&%~A = alloca ~A" a ty)
               (format s "~&store ~A %~A.arg, ~A* %~A" ty a ty a)))

       (multiple-value-bind (val deps) (compile-expr s body fctx)
         (format s "~&ret ~A" val)
         (format s "~&}")
         (loop for (f . ty) in deps
               do (compile-fundef s f ty ctx)))))))

(defun compile-type (ty ctx)
  (ematch ty
    ((type-t :name :integer :args nil) "i32")
    ((type-t :name :string  :args nil) "%std.String")

    ((type-t :name :array   :args (list len elty))
     (format nil "[~A x ~A]" len (compile-type elty ctx)))

    ((tvar :name n) (error (format nil "unresolved type (~A)" n)))))

(defun compile-expr (s e ctx)
  (let* ((nid     (ast-node-id e))
         (raw-ety (ctx-find-node-ty nid ctx))
         (ety     (compile-type raw-ety ctx)))
    (ematch e
      ((eblock stmts expr)
       (let-match ((deps (loop for stmt in stmts append (compile-stmt s stmt ctx))))
         (multiple-value-bind (rval rdeps) (compile-expr s expr ctx)
           (values rval (append deps rdeps)))))
      ((funcal name args)
       (let* ((funty-args (mapcar
                            (lambda-ematch
                              ((ast-node id)
                               (ctx-find-node-ty id ctx)))
                            args))
              (deps (list (cons (ctx-find-func name ctx)
                                (make-type-t :name :fun
                                             :args `(,@funty-args ,raw-ety)))))
              (argvs (mapcar (lambda (a) 
                               (multiple-value-bind (v ds) (compile-expr s a ctx)
                                 (setf deps (append deps ds))
                                 v))
                             args))
              (rval (gen-local)))
         (format s "~&~A = call ~A @~A(~{~A~^, ~})"
                 rval ety name argvs)

         (values (format nil "~A ~A" ety rval) deps)))

      ((varref name)
       (let ((rval (gen-local)))
         (format s "~&~A = load ~A, ~A* %~A" rval ety ety name)
         (values (format nil "~A ~A" ety rval) nil)))
      ((litera :val val :vty :integer) 
       (values (format nil "~A ~A" ety val) nil))
      ((litera :val val :vty :string)
       (let-match* ((len    (length val))
                    (arr-ty (format nil "[~A x i8]" len))
                    (val0 (emit-val s "alloca ~A" arr-ty))
                    (nil  (emit     s "store ~A c\"~A\", ~A* ~A"
                                    arr-ty val arr-ty val0))

                    (val1 (emit-val s "alloca ~A" ety))
                    (val2 (emit-val s "getelementptr ~A, ~A* ~A, i32 0, i32 0"
                                    ety ety val1))
                    (val3 (emit-val s "getelementptr ~A, ~A* ~A, i32 0, i32 1"
                                    ety ety val1))
                    (val4 (emit-val s "getelementptr ~A, ~A* ~A, i32 0, i32 0"
                                    arr-ty arr-ty val0))
                    (nil  (emit     s "store i32 ~A, i32* ~A" len  val2))
                    (nil  (emit     s "store i8* ~A, i8** ~A" val4 val3))
                    (val5 (emit-val s "load ~A, ~A* ~A" ety ety val1)))
         (values (format nil "~A ~A" ety val5)
                 nil))))))

(defun compile-stmt (s stmt ctx)
  (ematch stmt
    ((varlet :name name
             :val (and val (ast-node :id vid)))
     (let-match ((vty (compile-type (ctx-find-node-ty vid ctx) ctx)))
       (multiple-value-bind (val deps) (compile-expr s val ctx)
         (format s "~&%~A = alloca ~A" name vty)
         (format s "~&store ~A, ~A* %~A" val vty name)
         deps)))

    ((ast-node)
     (multiple-value-bind (_ deps) (compile-expr s stmt ctx)
       (declare (ignore _))
       deps))))

(defun instantiate-type (sty ity ctx)
  "Return new comp-ctx with free tvars in sty
     substituted for corresponding types in ity"

  (let-match* (((type-t :name ty1         :args aty1) sty)
               ((type-t :name (equal ty1) :args aty2) ity)
               (sub (mapcar (lambda (a b) (make-typ-eq :a a :b b))
                            aty1
                            aty2))
               (new-types (subst-ctx (comp-ctx-types ctx) sub))
               (new-ctx   (copy-comp-ctx ctx)))

    (setf (comp-ctx-types new-ctx) new-types)
    new-ctx))

#+nil
(defparameter *test-prg*
  "baz(a) = a;
   bar() = {
       h = \"abc\";
       baz(h)
   };
   main() = {
       bar(); 
       0
   };")

;; T14 unresolved
#+nil
(defparameter *test-prg*
  "
   bar() = id(\"abc\");
   id(x) = x;
   main() = {
       a = bar();
       0
   };
   ")

#+nil
(with-fresh-tvars
  (let* ((ast   (parse-module *test-prg*))
         (teqs  (infer-module ast *test-prg*))
         (types (mapcar (lambda-ematch ((typ-eq a b)
                                        (cons a b)))
                        teqs))
         (ctx   (make-comp-ctx :prg *test-prg* :module ast :types types)))
    ; (pprint-typed-ast *test-prg*)
    (compile-module t ctx)))
