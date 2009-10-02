;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.core.test
  (:use net.cgrand.parsley.core :reload)
  (:use [clojure.test :only [deftest is are]]))
  
(deftest misc
  (is (= [[["hello"] nil]] 
        (map next (interpreter-step1 conj "hello" false [nil [] [[op-string "hello"]]])))))
        
(def simple-lisp 
  (letfn [(expr [s eof cont]
            [[nil 0 (cons [op-alt [sym]
                       [op-cat 
                         [op-events [:open]] [op-string "("] 
                         [op-repeat [expr]] 
                         [op-string ")"] [op-events [:close]]]] cont)]])
          (sym [s eof cont]
            [[nil 0 (cons [op-string "x"] cont)]])]
    [expr]))
    
(interpreter-step conj [[nil [] [simple-lisp]]] "x" false)
(interpreter-step conj [[nil [] [simple-lisp]]] "((" false)
(interpreter-step conj [[nil [] [simple-lisp]]] "((x)x(x))" false)         