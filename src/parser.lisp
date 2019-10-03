(defpackage fyrec.parser
  (:use :cl :alexandria :let-plus :trivia)
  (:export
    =take
    =satisfiesp
    =satisfies
    =eof
    %map
    %subseq
    %any
    %or
    %list
    %destruc
    %some
    %maybe
    %named
    =seq
    =string
    parse))

(in-package :fyrec.parser)


(defun nth-position (n item seq)
  (let ((i -1))
    (position-if (lambda (c) (and (equal c item)
                                  (= n (incf i))))
                 seq)))

;;=============================================================================

;; INPUT
(defgeneric make-input (src))
(defgeneric input-first (input))
(defgeneric input-rest (input))
(defgeneric input-empty-p (input))
;; Subseq starting where start starts and ending where end starts
(defgeneric input-subseq (start end))
(defgeneric input-pos (input))
(defgeneric input-line-preview (input pos))

;;=============================================================================

(defstruct span
  (arr (error "need data") :type simple-string)
  (start 0 :type fixnum) ;; inclusing start
  (end   0 :type fixnum) ;; exclusive end 

  (line  0 :type fixnum)
  (chr   0 :type fixnum))

(defmethod make-input ((arr simple-string))
  (make-span :arr arr
             :start 0
             :end (length arr)
             :line 0
             :chr 0))

(defmethod input-first ((span span))
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (aref (span-arr   span)
        (span-start span)))

(defmethod input-rest ((span span))
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (let ((newline? (char= (input-first span)
                         #\newline)))
    (make-span :arr   (span-arr span)
               :start (the fixnum (1+ (span-start span)))
               :end   (span-end   span)

               :line  (if newline?
                          (1+ (span-line span))
                          (span-line span))
               :chr   (if newline? 
                          0
                          (1+ (span-chr span))))))

(defmethod input-empty-p ((span span))
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (>= (span-start span)
      (span-end   span)))

(defmethod input-subseq ((start span) (end span))
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (subseq (span-arr   start)
          (span-start start)
          (span-start end)))

(defmethod input-pos ((span span))
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (values
   (span-start span) 
   (span-line  span)
   (span-chr   span)))

(defmethod input-line-preview ((span span) pos)
  (let* ((str   (span-arr span))
         (line  (second pos))
         (chr   (third  pos))
         (start (if (= line 0)
                    0
                    (or (nth-position (1- line) #\newline str)
                        (error "Line index out of bounds"))))
         (end   (or (position #\newline str :start (1+ start))
                    (length str)))

         (line-view (subseq str start end))
         (line-mark (make-string (1+ chr) :initial-element #\space)))
    (setf (char line-mark chr) #\^)
    (list line-view
          line-mark)))

;;=============================================================================

;; parse failure is signaled by returning nil primary value

(defun =take/impl (input)
  (unless (input-empty-p input)
    (values 
      (input-rest input)
      (constantly (input-first input)))))

(defun =satisfies/impl (input fn &optional (parser #'=take/impl))
  (multiple-value-bind (rst val) (funcall parser input)
    (when rst
      (let ((val-eval (funcall val)))
        (when (funcall fn val-eval)
          (values 
            rst
            (constantly val-eval)))))))

(defun =eof/impl (input)
  (when (input-empty-p input)
    (values
      input
      (constantly nil))))

(defun %map/impl (input parser fn)
  (multiple-value-bind (rst val) (funcall parser input)
    (when rst
      (values
        rst
        (lambda () (funcall fn (funcall val)))))))

(defun %subseq/impl (input parser)
  (let ((rst (funcall parser input)))
    (when rst
      (values
        rst
        (lambda () (input-subseq input rst))))))


(defun %any/impl (input parser)
  (loop with rst = input ;; rest
        with lst = input ;; last
        with vals = '()
        while rst
        do (setf lst rst)
        do (let (val) 
             (setf (values rst val) (funcall parser rst))
             (when rst
               (push val vals)))
        finally (return (values
                          lst
                          (lambda ()
                            (mapcar #'funcall (reverse vals)))))))

(defun %or/impl (input &rest parsers)
  (loop for parser in parsers
        do (multiple-value-bind (rst val) (funcall parser input)
             (when rst
               (return (values rst val))))
        finally (return nil)))

(defun %list/impl (input &rest parsers)
  (loop for parser in parsers
        with rst = input
        with vals = '()
        if rst do (let (val)
                    (setf (values rst val) (funcall parser rst))
                    (when rst (push val vals)))
        else do (return nil)
        finally (return (values
                          rst
                          (lambda ()
                            (mapcar #'funcall (reverse vals)))))))

(defun %maybe/impl (input parser)
  (multiple-value-bind (rst val) (funcall parser input)
    (if rst
        (values rst val)
        (values input (constantly nil)))))

(defparameter *parse-failures* '())
(defparameter *furthest-parse-failure* '(-1 -1 -1))
(defun %named/impl (input name parser)
  (multiple-value-bind (rst val) (funcall parser input)
    (if rst
        (values rst val)
        (multiple-value-bind (pos lin chr) (input-pos input)
          (when (>= pos (first *furthest-parse-failure*))
            (setf *furthest-parse-failure* (list pos lin chr))
            (push (cons pos name) *parse-failures*))
          nil))))

; (defun %some/impl (input parser)
;   ()
;   )

;; Macros

(defmacro =take () '#'=take/impl)

(defmacro =satisfiesp (parser (v-id) &body body)
  `(lambda (in) (=satisfies/impl in (lambda (,v-id) ,@body) ,parser)))
(defmacro =satisfies ((v-id) &body body)
  `(lambda (in) (=satisfies/impl in (lambda (,v-id) ,@body))))

(defmacro =eof () '#'=eof/impl)

(defmacro %map (parser (v-id) &body body)
  `(lambda (in) (%map/impl in ,parser 
                           (lambda (,v-id) ,@body))))
(defmacro %subseq (parser)
  `(lambda (in) (%subseq/impl in ,parser)))

(defmacro %any (parser)
  `(lambda (in) (%any/impl in ,parser)))

(defmacro %or (&body parsers)
  `(lambda (in) (%or/impl in ,@parsers)))

(defmacro %list (&body parsers)
  `(lambda (in) (%list/impl in ,@parsers)))

(defmacro %destruc (parser (&rest pat) &body body)
  (let ((v-id (gensym))
        npat 
        ignores)
    (setf npat (mapcar (lambda (e)
                         (if (and (symbolp e)
                                  (string= (symbol-name e)
                                           "_"))
                             (first (push (gensym) ignores))
                             e))
                       pat))
    `(%map ,parser (,v-id)
       (destructuring-bind ,npat ,v-id
         (declare (ignore ,@ignores))
         ,@body))))

(defmacro %some (parser)
  `(%destruc (%list ,parser (%any ,parser))
            (fst rst)
            (cons fst rst)))

(defmacro %maybe (parser)
  `(lambda (in) (%maybe/impl in ,parser)))

(defmacro %named (name parser)
  `(lambda (in) (%named/impl in ,name ,parser)))

(defmacro =seq (seq &key (test #'equal))
  `(%map (%list ,(map 'list 
                      (lambda (e)
                        `(=satisfies (c)
                           (funcall ,test ,e c)))
                      seq))
         (val)
         (declare (ignore val))
         ,seq))

(defmacro =string (str)
  `(%map (%list ,@(loop for c across str
                        collect `(=satisfies (c)
                                   (char= ,c c))))
         (val)
         (declare (ignore val))
         ,str))

(defun parse (input parser &key (fname "-"))
  (let ((*parse-failures* '())
        (*furthest-parse-failure* '(-1 -1 -1))
        (input (make-input input)))
    (multiple-value-bind (rst val)
      (funcall parser input)
      (if rst
          (funcall val)
          (destructuring-bind (pos linum chrnum) *furthest-parse-failure*
            (format t "~&~A:~A:~A:expected one of: ~{~A~^, ~}~
                       ~{~%| ~A~}~
                       ~%"
                    fname
                    linum
                    chrnum
                    (loop for f in *parse-failures*
                          with r = '()
                          when (= (car f) pos)
                          do (setf r (adjoin (cdr f) r :test #'equal))
                          finally (return r))
                    (input-line-preview input *furthest-parse-failure*)))))))

#+nil
(time (parse "test" #.(%subseq (%any (=satisfies (c)
                               (member c '(#\e #\s #\t)))))))

(defmacro %ws () (=satisfies (c)
                   (member c '(#\space #\newline #\tab))))

(defmacro %id () (=satisfies (c) (lower-case-p c)))

#+nil
(parse "hel lo" #.(%destruc (%list (%subseq (%some (%id)))
                                   (%named "whitespace" (%ws))
                                   (%subseq (%some (%id))))
                            (a _ c)
                            (list a c)))


; (do-parse
;   (%some
;     (=satisfies (lambda (c) (char= #\a)))))
