(in-package :fyrec)

#|

CONSTRAINT GENERATION:
    program -> for each toplvl:
                 G(&ctx toplvl <>)

    TOPLVL
    ;; fundef is a combination of polymorphic let and lambda expr
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
    ;; varlet is not polumorphic (not a polymorphic let)
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

(defstruct ast-node (id (gen-node-id)) src-pos)
(defmacro defnode (name &rest r)
  `(defstruct (,name (:include ast-node)) ,@r))

;; Toplvl
(defnode fundef name args ret-ty body)

;; Type
(defnode etype name args)

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

(defstruct types-scope
  (vars  nil :read-only t)
  (types nil :read-only t))

(defparameter *cur-src-pos* nil)
(defstruct typ-eq a b (src-pos *cur-src-pos*))
(defstruct scm-eq sv ty (ty-scp nil :type types-scope) (src-pos *cur-src-pos*))
(defstruct ins-eq sv tv (src-pos *cur-src-pos*))

(defstruct tvar name)
(defstruct svar name)

(defstruct type-t  name args)
(defstruct union-t name typs) ;; TODO: <-
(defstruct trait-t name args) ;; TODO: <-

;;=============================================================================

(defparameter *builtin-types-scope*
  (make-types-scope :vars  `(("main" . ,(make-type-t :name :fun)))
		    :types `(("Int" . :integer)
			     ("Str" . :string))))

(defparameter *infer-current-prg* nil
  "The current program being inferred. For error messages.")

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
(defun ast-tvar-p (tv)
  (and (tvar-p tv)
       (listp (tvar-name tv))
       (eql :ast (first (tvar-name tv)))))

(defun etype->type-t (scope etype)
  (let-match (((etype name args) etype))
    (make-type-t :name (types-scope-get-typ scope name)
		 :args (mapcar (lambda (a) (etype->type-t scope a))
			       args))))

;; vars types
(defun types-scope-get-var (scope name)
 (let ((r (assoc name (types-scope-vars scope) :test #'equal)))
    (if r
        (cdr r)
        (error (format nil "var symbol not found in scope: ~A" name)))))
(defun types-scope-get-typ (scope name)
 (let ((r (assoc name (types-scope-types scope) :test #'equal)))
    (if r
        (cdr r)
        (error (format nil "type symbol not found in scope: ~A" name)))))

(defmacro map-types-scope-vars (scope (name) &body body)
  (let ((scope-s (gensym)))
    `(let ((,scope-s ,scope))
       (make-types-scope
	:types (types-scope-types ,scope-s)
	:vars  (let ((,name (types-scope-vars ,scope-s)))
		 ,@body)))))

(defmacro map-types-scope-types (scope (name) &body body)
  (let ((scope-s (gensym)))
    `(let ((,scope-s ,scope))
       (make-types-scope
	:vars (types-scope-vars ,scope-s)
	:types  (let ((,name (types-scope-types ,scope-s)))
		  ,@body)))))

(defun types-scope-set-var (scope name type)
  (map-types-scope-vars scope (current)
    `((,name . ,type) ,@current)))
(defun types-scope-set-typ (scope name type)
  (map-types-scope-types scope (current)
    `((,name . ,type) ,@current)))

(defun types-scope-set-vars (scope names types)
  (map-types-scope-vars scope (current)
    `(,@(mapcar #'cons names types) ,@current)))
(defun types-scope-set-typs (scope names types)
  (map-types-scope-types scope (current)
    `(,@(mapcar #'cons names types) ,@current)))

(defmacro types-scope-push-var (scope name type)
  `(setf ,scope (types-scope-set-var ,scope ,name ,type)))
(defmacro types-scope-push-typ (scope name type)
  `(setf ,scope (types-scope-set-typ ,scope ,name ,type)))

;;=============================================================================
;; CONSTRAINT GENERATION

(defun gen-eqs-module (m)
  (let ((scope (discover-toplvls *builtin-types-scope* m)))
    (loop for toplvl in (module-toplvls m)
          with eqs        = '()
          with toplvl-eqs = '()
          do
          (multiple-value-bind (eqs0 toplvl-eqs0)
            (ematch toplvl
              ((fundef) (gen-eqs-fundef scope toplvl)))

            (push eqs0        eqs)
            (push toplvl-eqs0 toplvl-eqs))
          finally
          (return `( ,@(reduce #'append (reverse toplvl-eqs))
                     ,@(reduce #'append (reverse eqs)))))))

(defun gen-eqs-fundef (scope f)
  (let-match* (((fundef name args ret-ty body id :src-pos *cur-src-pos*) f))
    ;; Polymorhpic or not determined in discover-toplvls at the moment
    (ematch (types-scope-get-var scope name)
      ;; polymorphic function
      ((and ty2 (svar))
       (let* ((ty1 (gen-tvar))
              (rty (if ret-ty
		       (etype->type-t scope ret-ty)
		       (gen-tvar)))
	      (aty '())
	      (aty-eqs (loop
			  for (name type) in args
			  for tvar = (gen-tvar)
			  with aty-eqs = '()
			  do (push tvar aty)
			  when type do
			    (push (make-typ-eq :a tvar
					       :b (etype->type-t scope type)
					       :src-pos (etype-src-pos type))
				  aty-eqs)
			  finally
			    (setf aty (reverse aty))
			    (return (reverse aty-eqs))))

	      (arg-names (mapcar #'car args))

              (eq0   (make-typ-eq :a (node-id->tvar id) :b ty1))

              (funty (make-type-t :name :fun
                                  :args (append aty (list rty))))
              (eq1   (make-typ-eq :a ty1
                                  :b funty))
              (eq2   (make-scm-eq :sv ty2
                                  :ty ty1
                                  :ty-scp scope))

	      (body-scope (types-scope-set-vars scope arg-names aty))
              (body-eqs (gen-eqs-expr body-scope body rty)))

         (assert-all-fun-args-used f args aty body-eqs)

         ;; toplvl scm-eqs should be first in the gen'd constraints
         (values `(,eq1 ,eq0 ,@aty-eqs ,@body-eqs)
                 `(,eq2))))

      ;; monomorphic function
      ;; ((and ty1 (tvar))
      ;;  (error "No function should be monomorphic!")
      ;;  (let* ((rty (if ret-ty
      ;; 		       (etype->type-t scope ret-ty)
      ;; 		       (gen-tvar)))
      ;; 	      (aty '())
      ;; 	      (aty-eqs (loop
      ;; 			  for (name type) in args
      ;; 			  for tvar = (gen-tvar)
      ;; 			  with aty-eqs = '()
      ;; 			  do (push tvar aty)
      ;; 			  when type do
      ;; 			    (push (make-typ-eq :a tvar
      ;; 					       :b (etype->type-t scope type)
      ;; 					       :src-pos (etype-src-pos type))
      ;; 				  aty-eqs)
      ;; 			  finally
      ;; 			    (setf aty (reverse aty))
      ;; 			    (return (reverse aty-eqs))))

      ;; 	      (arg-names (mapcar #'car args))

      ;;         (eq0   (make-typ-eq :a (node-id->tvar id) :b ty1))

      ;;         (funty (make-type-t :name :fun
      ;;                             :args (append aty (list rty))))
      ;;         (eq1   (make-typ-eq :a ty1
      ;;                             :b funty))

      ;; 	      (body-scope (types-scope-set-vars scope arg-names aty))
      ;;         (body-eqs (gen-eqs-expr body-scope body rty)))
      ;;    (values `(,eq1 ,eq0 ,@aty-eqs ,@body-eqs)
      ;;            `())))
      )))

#+nil
(defun gen-eqs-fundef (scope f)
  (let-match* (((fundef name args ret-ty body id :src-pos *cur-src-pos*) f))
    ;; Polymorhpic or not determined in discover-toplvls at the moment
    (ematch (types-scope-get-var scope name)
      ;; polymorphic function
      ((and ty2 (svar))
       (let* ((ty1 (gen-tvar))
              (rty (if ret-ty
		       (etype->type-t scope ret-ty)
		       (gen-tvar)))
	      (aty '())
	      (aty-eqs (loop
			  for (name type) in args
			  for tvar = (gen-tvar)
			  with aty-eqs = '()
			  do (push tvar aty)
			  when type do
			    (push (make-typ-eq :a tvar
					       :b (etype->type-t scope type)
					       :src-pos (etype-src-pos type))
				  aty-eqs)
			  finally
			    (setf aty (reverse aty))
			    (return (reverse aty-eqs))))

	      (arg-names (mapcar #'car args))

              (eq0   (make-typ-eq :a (node-id->tvar id) :b ty1))

              (funty (make-type-t :name :fun
                                  :args (append aty (list rty))))
              (eq1   (make-typ-eq :a ty1
                                  :b funty))
              (eq2   (make-scm-eq :sv ty2
                                  :ty ty1
                                  :ty-scp scope))

	      (body-scope (types-scope-set-vars scope arg-names aty))
              (body-eqs (gen-eqs-expr body-scope body rty)))

         (assert-all-fun-args-used f args aty body-eqs)

         ;; toplvl scm-eqs should be first in the gen'd constraints
         (values `(,eq1 ,eq0 ,@aty-eqs ,@body-eqs)
                 `(,eq2))))

      ;; monomorphic function
      ((and ty1 (tvar))
       (error "No function should be monomorphic!")
       (let* ((rty (if ret-ty
		       (etype->type-t scope ret-ty)
		       (gen-tvar)))
	      (aty '())
	      (aty-eqs (loop
			  for (name type) in args
			  for tvar = (gen-tvar)
			  with aty-eqs = '()
			  do (push tvar aty)
			  when type do
			    (push (make-typ-eq :a tvar
					       :b (etype->type-t scope type)
					       :src-pos (etype-src-pos type))
				  aty-eqs)
			  finally
			    (setf aty (reverse aty))
			    (return (reverse aty-eqs))))

	      (arg-names (mapcar #'car args))

              (eq0   (make-typ-eq :a (node-id->tvar id) :b ty1))

              (funty (make-type-t :name :fun
                                  :args (append aty (list rty))))
              (eq1   (make-typ-eq :a ty1
                                  :b funty))

	      (body-scope (types-scope-set-vars scope arg-names aty))
              (body-eqs (gen-eqs-expr body-scope body rty)))
         (values `(,eq1 ,eq0 ,@aty-eqs ,@body-eqs)
                 `()))))))

(defun gen-eqs-expr (scope expr ty)
  (let* ((*cur-src-pos* (ast-node-src-pos expr))
         (eq0  (make-typ-eq :a (node-id->tvar (ast-node-id expr))
			    :b ty)))
    `(,@(gen-eqs-expr/impl scope expr ty) ,eq0)))

(defun gen-eqs-expr/impl (scope expr ty)
  (ematch expr
    ((eblock stmts expr)
     (loop for stmt in stmts
           with cscope = scope
           with eqs  = '()
           do (let (eqs0)
                (setf (values eqs0 cscope)
                      (gen-eqs-stmt cscope stmt))
                (push eqs0 eqs))
           finally
           (return (let* ((eeqs (gen-eqs-expr cscope expr ty)))
                     `(,@(reduce #'append (reverse eqs)) ,@eeqs)))))

    ((varref name)
     (let-match (((and vty (or (tvar)
			       (type-t)))
		  (types-scope-get-var scope name)))
       (list (make-typ-eq :a ty
                          :b vty))))

    ((funcal name args)
     (if (> (length args) 0)
	 (let-match* ((aty (mapcar (lambda (_) (declare (ignore _)) (gen-tvar))
				   args))
		      (fty (types-scope-get-var scope name))

		      (funty (make-type-t :name :fun :args (append aty (list ty))))
		      (eq1   (make-ins-eq :sv fty :tv funty))

		      (a-eqs (mapcar (lambda (arg ty)
				       (gen-eqs-expr scope arg ty))
				     args aty)))

	   `(,eq1 ,@(reduce #'append a-eqs)))

	 (let-match* ((aty (mapcar (lambda (_) (declare (ignore _)) (gen-tvar))
				   args))
		      (fty (types-scope-get-var scope name))

		      (funty (make-type-t :name :fun :args (append aty (list ty))))
		      (eq1   (make-ins-eq :sv fty :tv funty))

		      (a-eqs (mapcar (lambda (arg ty)
				       (gen-eqs-expr scope arg ty))
				     args aty)))

	   `(,eq1 ,@(reduce #'append a-eqs)))
	 ))

    ;; ((funcal name args)
    ;;  (let-match* ((aty (mapcar (lambda (_) (declare (ignore _)) (gen-tvar))
    ;;                            args))
    ;;               (fty (types-scope-get-var scope name))

    ;;               (funty (make-type-t :name :fun :args (append aty (list ty))))
    ;;               (eq1   (cond ((svar-p fty) (make-ins-eq :sv fty :tv funty))
    ;;                            ((tvar-p fty) (make-typ-eq :a fty :b funty))))

    ;;               (a-eqs (mapcar (lambda (arg ty)
    ;;                                (gen-eqs-expr scope arg ty))
    ;;                              args aty)))
    ;;    `(,eq1 ,@(reduce #'append a-eqs))))

    ((litera vty) (list (make-typ-eq
                          :a ty
                          :b (make-type-t :name vty))))))

(defun gen-eqs-stmt (scope stmt)
  (ematch stmt
    ((varlet name val)
     (let* ((ty0 (gen-tvar)))
       (values (gen-eqs-expr scope val ty0)
	       (types-scope-set-var scope name ty0))))
    (_ (values (gen-eqs-expr scope stmt (gen-tvar))
               scope))))

(defun discover-toplvls (scope m)
  (loop for toplvl in (module-toplvls m)
        do (ematch toplvl
             ;; All functions are svars since they can all be polymorhpic
             ((fundef name args)
              ;; funcs of arity=0 are cannot be polymorphic
	      ;; TODO: make 0-arity funcs polymorphic as in normal polymorphic functions
	      ;;(types-scope-push-var scope name (gen-svar)) BEFORE SPONGE
	      (types-scope-push-var scope name (gen-svar))

	      ;; (types-scope-push-var OLD
	      ;;  scope name (if args
	      ;; 		      (gen-svar)
	      ;; 		      (gen-tvar)))
	      ))

        finally (return scope)))

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
	     ;; (replace ast-tvars by tvars but not the other way around)
             ((or (typ-eq :a (and tv (tvar))
                          :b (and x (not (satisfies ast-tvar-p)))
                          :src-pos p)
                  (typ-eq :a (and x (not (satisfies ast-tvar-p)))
                          :b (and tv (tvar))
                          :src-pos p))
              (if (occurs? tv x)
                  (error (format nil "recursive type for ~S" tv))
                  (let ((sub (list (make-typ-eq :a tv :b x :src-pos p))))
                    (setf eqs (subst-eqs     eqs sub))
                    (setf sol (compose-subst sol sub))))) ;; unswaped

             ;; <type> args... = <type> args...
             ((guard (typ-eq :a (type-t :name an :args a-args)
                             :b (type-t :name bn :args b-args)
                             :src-pos p)
                     (and (equal an bn)
                          (= (length a-args)
                             (length b-args))))
              (loop for a-aty in a-args
                    for b-aty in b-args
                    do (push (make-typ-eq :a a-aty
                                          :b b-aty
                                          :src-pos p)
                             eqs)))
             ;; Type mismatch
             ((typ-eq a b src-pos)
              (let ((err (format nil "type mismatch: ~
                                      ~/fyrec:pprint-ty/ and ~/fyrec:pprint-ty/"
                                 a b)))
                   (print-error-at-pos *infer-current-prg* err src-pos
                                    :make-in t)
                   (error "type mismatch"))))

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
                                  ((ins-eq tv src-pos)
                                   (make-typ-eq :a tv
                                                :b (inst-scm e)
                                                :src-pos src-pos)))
                                i-eqs))
                       (sub (e-unify e-eqs)))


                  (setf sol (compose-subst sol sub))

                  ;; ======
		  #|
                  (when (match e ((scm-eq ; :sv (svar :name 'S1)
                                          ) t))
                    (break (format nil "break~%e: ~/fyrec:pprint-eq/~2%~
                                        i-eqs: ~/fyrec:pprint-eqs/~2%~
                                        others (eqs): ~/fyrec:pprint-eqs/~2%~
                                        gened-eqs (e-eqs): ~/fyrec:pprint-eqs/~2%~
                                        sub: ~/fyrec:pprint-eqs/~2%~
                                        sol: ~/fyrec:pprint-eqs/"
                                   e i-eqs eqs e-eqs sub sol)))
		  |#
                  )))

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
    ((typ-eq a b src-pos)
     (make-typ-eq :a (subst-ty a sub)
                  :b (subst-ty b sub)
                  :src-pos src-pos))
    ((scm-eq sv ty ty-scp src-pos)
     (make-scm-eq :sv sv
                  :ty (subst-ty ty sub)
                  :ty-scp (subst-types-scope-vars ty-scp sub)
                  :src-pos src-pos))
    ((ins-eq sv tv src-pos)
     (make-ins-eq :sv sv
                  :tv (subst-ty tv sub)
                  :src-pos src-pos))))

(defun subst-ty (ty sub)
  "Substitute the tvars of ty according to sub"
  (ematch ty
    ((tvar) (or (get-subst sub ty) ty))
    ((svar) ty)
    ((type-t name args)
     (make-type-t :name name
                  :args (mapcar (lambda (aty) (subst-ty aty sub))
                                args)))))

(defun subst-types-scope-vars (scope sub)
  "Substitute the tvars of the right sides of eqs of scope var entries according to sub"
  (map-types-scope-vars scope (v)
    (mapcar (lambda-ematch ((cons n ty)
			    (cons n (subst-ty ty sub))))
	    v)))

(defun compose-subst (sub1 sub2)
  "Compose two substitutions such that (s2 ∘ s1)(x) = s2(s1(x))"
  ;; nconc modifies all but last arg
  (nconc (mapcar (lambda-ematch ((typ-eq a b src-pos)
                                 (make-typ-eq :a a
                                              :b (subst-ty b sub2)
                                              :src-pos src-pos)))
                 sub1)
         sub2))

(defun inst-scm (s-eq)
  "instantiate bound variables in the scheme with fresh free variables"
  (let-match* (((scm-eq ty src-pos) s-eq)
               (bound-vars (scm-eq-bound-vars s-eq))
               (instantiation-sub (mapcar (lambda (tv)
                                            (make-typ-eq :a tv
                                                         :b (gen-tvar)
                                                         :src-pos src-pos))
                                          bound-vars)))
    (subst-ty ty instantiation-sub)))

(defun scm-eq-bound-vars (e &key debug)
  (ematch e
    ((scm-eq sv ty ty-scp)
     (let ((ty-ftvs  (ftv-ty ty))
	   (ctx-ftvs (ftv-types-scope-vars ty-scp)))
       (let ((bound-vars (set-difference ty-ftvs ctx-ftvs :test #'equal)))
	 (format t "~&bound vars of ~S is ~S~%" sv bound-vars)
	 bound-vars)))))

(defun ftv-ty (ty)
  (ematch ty
    ((tvar) (list ty))
    ((svar) '())
    ((type-t args)
     (reduce (lambda (a b) (union a b :test #'equal))
             (mapcar #'ftv-ty args)
             :initial-value '()))))

(defun ftv-types-scope-vars (scope)
  "Find all the ftvs from the right hand sides of variable definitions in the scope"
  (reduce (lambda (a b) (union a b :test #'equal))
          (mapcar (lambda-ematch ((cons _ ty)
                                  (ftv-ty ty)))
                  (types-scope-vars scope))

          :initial-value '()))

(defun infer-module (m prg)
  (let* ((*infer-current-prg* prg)
	 (unsolved-eqs (gen-eqs-module m)))
    (values (solve-eqs unsolved-eqs) unsolved-eqs)))

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
;; VALIDATING

(defun assert-all-fun-args-used (fun args aty eqs)
  "If not all fun args are used in the body, the type of the function
will never be resolved as the eq for the unused arg will never have
a right handn side"
  (loop for arg in args
        for ty in aty
        with bad = nil
        do
        (when (notany (lambda-ematch ((typ-eq a b) (or (occurs? ty a)
                                                       (occurs? ty b)))
                                     ((ins-eq tv) (occurs? ty tv))
                                     ((scm-eq :ty sty) (occurs? ty sty)))
                      eqs)
          (setf bad t)
          (let-match (((fundef src-pos) fun))
            (print-error-at-pos
              *infer-current-prg*
              (format nil "unused function argument: ~A" arg)
              src-pos
              :make-in t)))
        finally
        (when bad
          (error "unused argument(s) in function definition"))))

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
       (format s "~A" pn)))))

(defparameter *pprint-tvar* nil)
(defun pprint-ty (s ty &rest r)
  (declare (ignore r))
  (ematch ty
    ((or (tvar name)
         (svar name))
     (if *pprint-tvar*
         (pprint-tvar s ty)
	 (format s "~A" name)))

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
             ty (scm-eq-bound-vars e :debug t) sv))))

(defun pprint-eqs (s eqs &rest r)
  (loop for e in eqs do
        (fresh-line s)
        (apply #'pprint-eq `(,s ,e ,@r))))

(defun pprint-typed-ast (prg &key print-unsolved-eqs print-sol)
  (with-fresh-tvars
    (let* ((*pprint-tvar* nil)
           (*ast-node-count* 0)
           (ast (parse-module prg))
	   (sol (multiple-value-bind (sol unsolved-eqs) (infer-module ast prg)
		  (when print-unsolved-eqs
		    (format t "~&~%unsolved eqs:~%")
		    (pprint-eqs t unsolved-eqs))
		  sol)))
      (when print-sol
	(format t "~&~%solution:~%")
	(pprint-eqs t sol))
      (fresh-line)
      (sort sol (lambda-ematch* (((typ-eq :src-pos (list abs-a _ _))
                                  (typ-eq :src-pos (list abs-b _ _)))
                                 (< abs-a abs-b))))
      (loop for e in sol do
            (match e ((typ-eq :a tya ; (tvar :name (list :ast _))
                              :b ty
                              :src-pos src-pos)
                      (let ((msg (format nil "type: ~A = ~A"
                                         (pprint-ty nil tya)
                                         (pprint-ty nil ty))))
                        (print-error-at-pos prg msg src-pos :make-in t)))))

      ; (fresh-line)
      ; (format t "~A" ast)
      )))

#+nil
(defparameter *test-prg*
  "
   Foo = {
       i   Int,
       str String
   };

   Foo.T = {T, T};

   
   foo() = bar(1);
   bar(b) = {
       b
   };
   baz(a) = a;")

#+nil
(defparameter *test-prg*
  "
  baz(a) = a;
  bar() = baz(123);
  foo() = bar();
")

#+nil
(defparameter *test-prg*
  "
  bar(a) = a;
  foo() = bar(123);
  baz() = bar(\"string\");
")

#+nil
(pprint-typed-ast *test-prg* :print-unsolved-eqs t :print-sol t)

#+nil
(with-fresh-tvars
  (let* ((*pprint-tvar* nil)
         (*ast-node-count* 0)
         (ast (parse-module *test-prg*))
         (sol (infer-module ast *test-prg*)))

    (values (pprint-eqs t sol)
            (ast-eqs->table sol)
            ast)))

#+nil
(pprint-eqs t (gen-eqs-module (parse-module *test-prg*)))
