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

(def hello [op-string "hello"])
(def world [op-string "world"])

(defn append [val event]
  (cond 
    (= "" event) 
      val
    (and (string? event) (string? (peek val)))
      (conj (pop val) (str (peek val) event))
    :else
      (conj val event)))

(defn- eq [expected results]
  (= (set (map (partial cons nil) expected)) 
    (set results)))

(deftest test-ops
  (are [cont s results] 
    (eq results 
      (interpreter-step1 append s [nil [] cont]))
    [hello] "hello", [[["hello"] nil]]
    [hello] "hel", [[["hel"] [[op-string "lo"]]]]
    [hello] "", [[[] [hello]]]
    [hello] "helo", nil
    [hello] nil, nil
    [[op-string ""]] nil, nil
  
    [[op-cat hello world]] "hello", [[["hello"] [world]]] 
    [[op-cat hello world]] "", [[[] [hello world]]] 
    [[op-cat hello world]] nil, nil 
  
    [[op-alt hello world]] "hello", [[["hello"] nil]] 
    [[op-alt hello world]] "world", [[["world"] nil]] 
    [[op-alt hello world]] "w", [[["w"] [[op-string "orld"]]]] 
    [[op-alt hello world]] "", [[[] [hello]] [[] [world]]] 
    [[op-alt hello world]] nil, nil 
  
    [[op-alt hello world]] "hello", [[["hello"] nil]] 
    [[op-alt hello world]] "world", [[["world"] nil]] 
    [[op-alt hello world]] "w", [[["w"] [[op-string "orld"]]]] 
    [[op-alt hello world]] "", [[[] [hello]] [[] [world]]] 
    [[op-alt hello world]] nil, nil
    
    [[op-repeat hello]] "", [[[] [hello [op-repeat hello]]] [[] nil]]  
    [[op-repeat hello]] "h", [[["h"] [[op-string "ello"] [op-repeat hello]]]]  
    [[op-repeat hello]] "helloh", [[["helloh"] [[op-string "ello"] [op-repeat hello]]]]  
    [[op-repeat hello]] nil, [[[] nil]]
    
    [[op-eof]] "a", nil  
    [[op-eof]] "", [[[] [[op-eof]]]]  
    [[op-eof]] nil, [[[] nil]]  
  ))
        
(comment
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
)