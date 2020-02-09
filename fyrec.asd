(defsystem "fyrec"
  :version "0.1.0"
  :author "Javier A. Pollak"
  :license "GPL2"
  :depends-on (alexandria let-plus trivia maxpc)
  :components ((:module "src"
                :components
                ((:file "parser")
                 (:file "fyrec")
                 (:file "infer")
                 (:file "ast-gen")
		 (:file "std-lib")
                 (:file "compile"))))
  :description "A prototype fyre compiler"
  :long-description
  #.(read-file-string
     (subpathname *load-pathname* "README.md"))
  :in-order-to ((test-op (test-op "fyrec/test"))))

(defsystem "fyrec/test"
  :author "Javier A. Pollak"
  :license "GPL2"
  :depends-on (fyrec parachute)
  :components ((:module "tests"
                :components
                ((:file "fyrec"))))
  :description "Test system for fyrec"
  :perform (asdf:test-op (op c) (uiop:symbol-call :parachute :test :fyrec-test)))
