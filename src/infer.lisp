(in-package :fyrec)

#|

CONSTRAINT GENERATION:
    program -> for each toplvl:
                 G(&ctx toplvl <>)

    TOPLVL
    fundef -> fresh tvar aty... rty, ty1
              fresh svar ty2

              and gen:
                    ;;G(ctx, fun_form, ty1) {

                    ty1 =e (tfun (aty...) rty)
                    G(ctx[argn = aty]... body rty)

                    ;;}

                    ;; BODY OF LET G(ctx[funname = ty2] rest ty)
                    ;; rest of forms (no real type)

                    ty2 =s ty1 ctx

    STMT
    varlet -> fresh tvar ty0 and gen: ty e= UNIT
                   G(ctx e ty0)
                   ctx[vn = ty0]

    EXPR
    eblock -> for each stmt:
                G(&ctx stmt <fresh tvar>)
              last expr
                G(ctx expr ty)

    varref -> find tvar vty in ctx   and gen: ty =e vty
           ;; OR find svar vty in ctx   and gen: ty =i vty

    ;; funcal -> fresh tvar aty... and gen: G(ctx funref (tfun (aty...) ty))
    ;;                                      G(ctx arg aty)...

    funcal -> fresh tvar aty...
              find  svar fty in ctx
              and gen:
                (tfun (aty...) ty) =i fty
                G(ctx arg aty)...

    litera -> get literal ty0   and gen: ty =e ty0


|#
;;=============================================================================

(defstruct module toplvls)

(defstruct ast-node (id (gen-node-id)))
(defmacro defnode (name &rest r)
  `(defstruct (,name (:include ast-node)) ,@r))

;; Toplvl
(defnode fundef name args body)

;; Statement
(defnode varlet name val)

;; Expr
(defnode eblock stmts expr)
(defnode varref name)
(defnode funcal name args)
(defnode litera val vty)

(defparameter *ast-node-count* 0)
(defun gen-node-id ()
  (let ((r *ast-node-count*))
    (incf *ast-node-count*)
    r))

;;=============================================================================

(defstruct typ-eq a b)
(defstruct scm-eq sv ty ty-ctx)
(defstruct ins-eq sv tv)

(defstruct tvar name)
(defstruct svar name)

(defstruct type-t  name args)
(defstruct union-t name typs) ;; TODO: <-
(defstruct trait-t name args) ;; TODO: <-

;;=============================================================================

(defparameter *tvar-count* 0)
(defun gen-var (&optional (v 'T))
  (let ((n (incf *tvar-count*)))
    (intern (concatenate 'string
                         (write-to-string v)
                         (write-to-string n)))))

(defun gen-tvar (&optional (v 'T)) (make-tvar :name (gen-var v)))
(defun gen-svar (&optional (v 'S)) (make-svar :name (gen-var v)))

(defun node-id->tvar (id)
  (make-tvar :name (list :ast id)))

(defun ctx-get (ctx name)
  (let ((r (assoc name ctx :test #'equal)))
    (if r
        (cdr r)
        (error (format nil "symbol not found in context: ~A" name)))))

;;=============================================================================
;; CONSTRAINT GENERATION

(defun gen-eqs-module (m)
  (let ((ctx (discover-toplvls m)))
    (loop for toplvl in (module-toplvls m)
          with eqs        = '()
          with toplvl-eqs = '()
          do
          (multiple-value-bind (eqs0 toplvl-eqs0)
            (ematch toplvl
              ((fundef) (gen-eqs-fundef ctx toplvl)))

            (push eqs0        eqs)
            (push toplvl-eqs0 toplvl-eqs))
          finally
          (return `( ,@(reduce #'append (reverse toplvl-eqs))
                     ,@(reduce #'append (reverse eqs)))))))

(defun gen-eqs-fundef (ctx f)
  (let-match* (((fundef name args body id) f)
               ((and ty2 (svar)) (ctx-get ctx name))
               (ty1 (gen-tvar))
               (rty (gen-tvar))
               (aty (mapcar (lambda (_)
                              (declare (ignore _))
                              (gen-tvar))
                            args))

               (eq0   (make-typ-eq :a (node-id->tvar id) :b ty1))

               (funty (make-type-t :name 'fun
                                   :args (append aty (list rty))))
               (eq1   (make-typ-eq :a ty1
                                   :b funty))
               (eq2   (make-scm-eq :sv ty2
                                   :ty ty1
                                   :ty-ctx ctx))

               (body-ctx (append ctx (mapcar #'cons args aty)))
               (eqs (gen-eqs-expr body-ctx body rty)))

    (values `(,eq1 ,eq0 ,@eqs)
            `(,eq2)))) ;; toplvl scm-eqs should be first in the gen'd constraints

(defun gen-eqs-expr (ctx expr ty)
  (let ((eq0  (make-typ-eq :a (node-id->tvar (ast-node-id expr))
                           :b ty)))
    `(,@(gen-eqs-expr/impl ctx expr ty) ,eq0)))

(defun gen-eqs-expr/impl (ctx expr ty)
  (ematch expr
    ((eblock stmts expr)
     (loop for stmt in stmts
           with cctx = ctx
           with eqs  = '()
           do (let (eqs0)
                (setf (values eqs0 cctx)
                      (gen-eqs-stmt cctx stmt))
                (push eqs0 eqs))
           finally
           (return (let* ((eeqs (gen-eqs-expr cctx expr ty)))
                     `(,@(reduce #'append (reverse eqs)) ,@eeqs)))))

    ((varref name)
     (let-match (((and vty (tvar)) (ctx-get ctx name)))
       (list (make-typ-eq :a ty
                          :b vty))))

    ((funcal name args)
     (let-match* ((aty (mapcar (lambda (_) (declare (ignore _)) (gen-tvar))
                               args))
                  ((and fty (svar)) (ctx-get ctx name))

                  (funty (make-type-t :name 'fun :args (append aty (list ty))))
                  (eq1   (make-ins-eq :sv fty :tv funty))

                  (a-eqs (mapcar (lambda (arg ty)
                                   (gen-eqs-expr ctx arg ty))
                                 args aty)))
       `(,eq1 ,@(reduce #'append a-eqs))))

    ((litera vty) (list (make-typ-eq
                          :a ty
                          :b (make-type-t :name vty))))))

(defun gen-eqs-stmt (ctx stmt)
  (ematch stmt
    ((varlet name val)
     (let* ((ty0 (gen-tvar)))
       (values (gen-eqs-expr ctx val ty0)
               `((,name . ,ty0) ,@ctx))))
    (_ (values (gen-eqs-expr ctx stmt (gen-tvar))
               ctx))))

(defun discover-toplvls (m)
  (loop for toplvl in (module-toplvls m)
        with ctx = '()
        do (ematch toplvl
             ;; All functions are svars since they call all be polymorhpic
             ((fundef name) (push (cons name (gen-svar)) ctx)))
        finally (return ctx)))

;;=============================================================================
;; CONSTRAINT SOLVING

(defun solve-eqs (eqs)
  (let* ((e-eqs  (remove-if-not #'typ-eq-p eqs))
         (si-eqs (remove-if     #'typ-eq-p eqs))

         (sub1 (e-unify  e-eqs))
         (sub2 (si-unify (subst-eqs si-eqs sub1))))
    (compose-subst sub1 sub2)))

(defun e-unify (eqs)
  (loop with sol = '()
        with eqs = eqs
        while eqs
        do (ematch (pop eqs)
             ;; NO-OP
             ;; x == x
             ((guard (typ-eq a b)
                     (equal  a b)) nil)

             ;; tvar = x | x = tvar
             ((or (typ-eq :a (and tv (tvar))
                          :b x)
                  (typ-eq :a x
                          :b (and tv (tvar))))
              (if (occurs? tv x)
                  (error (format nil "recursive type for ~S" tv))
                  (let ((sub (list (make-typ-eq :a tv :b x))))
                    (setf eqs (subst-eqs     eqs sub))
                    (setf sol (compose-subst sol sub)))))

             ;; <type> args... = <type> args...
             ((guard (typ-eq :a (type-t :name an :args a-args)
                             :b (type-t :name bn :args b-args))
                     (and (equal an bn)
                          (= (length a-args)
                             (length b-args))))
              (loop for a-aty in a-args
                    for b-aty in b-args
                    do (push (make-typ-eq :a a-aty
                                          :b b-aty)
                             eqs)))
             ;; Type mismatch
             ((typ-eq a b)
              (error (format nil "type mismatch: ~
                                  ~/fyrec:pprint-ty/ and ~/fyrec:pprint-ty/" a b))))

        finally (return sol)))

(defun si-unify (eqs)
  (loop with sol = '()
        with eqs = eqs
        while eqs
        do (ematch (pop eqs)
             ((and (scm-eq) e)
              (let (i-eqs
                    (pred (lambda-ematch
                            ((ins-eq :sv sv) (equal (scm-eq-sv e) sv))
                            ((scm-eq) nil))))
                (setf i-eqs (remove-if-not pred eqs))
                (setf eqs   (remove-if     pred eqs))
                (let* ((e-eqs (mapcar
                              (lambda-ematch
                                ((ins-eq tv)
                                 (make-typ-eq :a tv
                                              :b (inst-scm e))))
                              i-eqs))
                       (sub (e-unify e-eqs)))
                  (setf sol (compose-subst sol sub)))))

             ((ins-eq)
              (error "BUG: bad order of generated si-eqs.
                      (instantiations must come after scheme equations)")))

        finally (return sol)))

(defun occurs? (tv ty)
  "Does tvar tv occur in type ty?"
  (ematch ty
    ((tvar) (equal tv ty))
    ((type-t args) (some (lambda (aty) (occurs? tv aty))
                         args))))

(defun get-subst (sub tv)
  "Find the substitution for tvar tv in sub or return NIL"

  ;; Find the first match
  ;; (all following matches may be garbage since this works like an alist)
  (some (lambda-ematch ((guard (typ-eq a b)
                               (equal a tv)) b)
                       ((typ-eq) nil))
        sub))

(defun subst-eqs (eqs sub)
  "Substitute the tvars of both sides of eqs according to sub"
  (mapcar (lambda (e) (subst-eq e sub)) eqs))

(defun subst-eq (e sub)
  "Substitute the tvars of both sides of e according to sub"
  (ematch e
    ((typ-eq a b)
     (make-typ-eq :a (subst-ty a sub)
                  :b (subst-ty b sub)))
    ((scm-eq sv ty ty-ctx)
     (make-scm-eq :sv sv
                  :ty (subst-ty ty sub)
                  :ty-ctx (subst-ctx ty-ctx sub)))
    ((ins-eq sv tv)
     (make-ins-eq :sv sv
                  :tv (subst-ty tv sub)))))

(defun subst-ty (ty sub)
  "Substitute the tvars of ty according to sub"
  (ematch ty
    ((tvar) (or (get-subst sub ty) ty))
    ((svar) ty)
    ((type-t name args)
     (make-type-t :name name
                  :args (mapcar (lambda (aty) (subst-ty aty sub))
                                args)))))

(defun subst-ctx (ctx sub)
  "Substitute the tvars of the right sides of eqs of ctx according to sub"
  (mapcar (lambda-ematch ((cons n ty)
                          (cons n (subst-ty ty sub))))
          ctx))

(defun compose-subst (sub1 sub2)
  "Compose two substitutions such that (s2 ∘ s1)(x) = s2(s1(x))"
  ;; nconc modifies all but last arg
  (nconc (mapcar (lambda-ematch ((typ-eq a b)
                                 (make-typ-eq :a a
                                              :b (subst-ty b sub2))))
                 sub1)
         sub2))

(defun inst-scm (s-eq)
  "instantiate bound variables in the scheme with fresh free variables"
  (let-match* (((scm-eq ty) s-eq)
               (bound-vars (scm-eq-bound-vars s-eq))
               (instantiation-sub (mapcar (lambda (tv)
                                            (make-typ-eq :a tv
                                                         :b (gen-tvar)))
                                          bound-vars)))
    (subst-ty ty instantiation-sub)))

(defun scm-eq-bound-vars (e)
  (ematch e
    ((scm-eq ty ty-ctx)
     (let ((ty-ftvs  (ftv-ty ty))
           (ctx-ftvs (ftv-ctx ty-ctx)))
       (set-difference ty-ftvs ctx-ftvs :test #'equal)))))

(defun ftv-ty (ty)
  (ematch ty
    ((tvar) (list ty))
    ((svar) '())
    ((type-t args)
     (reduce (lambda (a b) (union a b :test #'equal))
             (mapcar #'ftv-ty args)
             :initial-value '()))))

(defun ftv-ctx (ctx)
  (reduce (lambda (a b) (union a b :test #'equal))
          (mapcar (lambda-ematch ((cons _ ty)
                                  (ftv-ty ty)))
                  ctx)

          :initial-value '()))

(defun infer-module (m)
  (solve-eqs (gen-eqs-module m)))

(defun ast-eqs->table (eqs)
  (let ((table (make-hash-table :test #'equal)))
    (mapcar (lambda-ematch ((typ-eq :a (tvar :name (list :ast id))
                                    :b ty)
                            (setf (gethash id table) ty)))
            (remove-if-not
              (lambda-ematch ((typ-eq :a (tvar :name (list :ast _))) t)
                             ((or (typ-eq)
                                  (scm-eq)
                                  (ins-eq)) nil))
              eqs))
    table))

;;=============================================================================
;; PRINTING

(defparameter *pretty-tvar-count* 0)
(defparameter *pretty-tvar-names* (make-hash-table :test #'equal))
(defmacro with-fresh-tvars (&body body)
  `(let ((*tvar-count* 0)
         (*pretty-tvar-count* 0)
         (*pretty-tvar-names* (make-hash-table :test #'equal)))
     ,@body))

(defun num->letters (num)
  "Return a for 0 and z for 25. Every wrap adds a letter: 26 => aa, 27 => bb"
  (let* ((numchars (1+ (floor (/ num 26))))
         (letter   (mod num 26))
         (lchar    (code-char (+ letter (char-code #\A)))))
    (make-string numchars :initial-element lchar)))

(defun pprint-tvar (s tv &rest r)
  (declare (ignore r))
  (ematch tv
    ((or (tvar) (svar))
     (let ((pn (gethash tv *pretty-tvar-names*)))
       (unless pn
         (setf pn (num->letters *pretty-tvar-count*))
         (incf *pretty-tvar-count*)
         (setf (gethash tv *pretty-tvar-names*) pn))
       (princ pn s)))))

(defparameter *pprint-tvar* nil)
(defun pprint-ty (s ty &rest r)
  (declare (ignore r))
  (ematch ty
    ((or (tvar name)
         (svar name))
     (if *pprint-tvar*
         (pprint-tvar s ty)
         (princ name s)))

    ((type-t name args)
     (format s "~A(~{~/fyrec:pprint-ty/~^, ~})"
             name args))))

(defun pprint-eq (s e &rest r)
  (declare (ignore r))
  (ematch e
    ((typ-eq a b)
     (format s "~/fyrec:pprint-ty/  = ~/fyrec:pprint-ty/" a b))

    ((ins-eq sv tv)
     (format s "~/fyrec:pprint-ty/ i= ~/fyrec:pprint-ty/" sv tv))

    ((scm-eq sv ty)
     (format s "~/fyrec:pprint-ty/ s= forall ~{~/fyrec:pprint-ty/~^, ~}. ~
                                             ~/fyrec:pprint-ty/"
             sv (scm-eq-bound-vars e) ty))))

(defun pprint-eqs (s eqs &rest r)
  (loop for e in eqs do
        (fresh-line s)
        (apply #'pprint-eq `(,s ,e ,@r))))

#+nil
(defparameter *test-prg*
  "foo(a) = bar(1);
   bar(b) = {
       b = { baz(foo(b)) };
       b
   };
   baz(a) = a;")

#+nil
(with-fresh-tvars
  (let* ((*pprint-tvar* nil)
         (*ast-node-count* 0)
         (ast (parse-module *test-prg*))
         (sol (infer-module ast)))

    (values (pprint-eqs t sol)
            (ast-eqs->table sol)
            ast)))

#+nil
(pprint-eqs t (gen-eqs-module (parse-module *test-prg*)))
