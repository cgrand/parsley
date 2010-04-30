(ns net.cgrand.parsley.test
  (:require [net.cgrand.parsley.glr :as core])
  (:use net.cgrand.parsley)
  (:use clojure.test))

(def sexp 
  (grammar {:space :whitespace?
            :main [:expr*]}
    
    :expr- #{:atom :list :vector :set :map}
    :atom (token {\a \z \A \Z \- \- \0 \9 \. \.}+ 
            (?! {\a \z \A \Z \- \- \0 \9 \. \.}))
    :list ["(" :expr* ")"]
    :vector ["[" :expr* "]"]
    :set ["#{" :expr* "}"]
    :map ["{" :expr* "}"]
    
    :whitespace (token #{\space \tab \newline}+ (?! #{\space \tab \newline}))))

(def table (apply core/lr-table sexp))
(def sop [[(list 0) () nil]])

(defn parse [table s]
  (-> sop (core/step table s) (core/step table nil)))

(defn vec-tree [parse-tree]
  (cond
    (map? parse-tree) 
      (into [(:tag parse-tree)] (->> parse-tree :content (map vec-tree)))
    (vector? parse-tree)
      (vec (map vec-tree parse-tree)) 
    :else parse-tree))

(defn parse-tree [table s]
  (core/read-events (-> (parse table s) first second) s))

(deftest one-chunk
  (are [r s] (= r ({0 :fail 1 :match} (count (parse table s)) :matches))
    :match ""
    :match "hello"
    :match "  hello  "
    :match "(hello)"
    :match "(  hello  )"
    :match "(hello world)"
    :match "(eq r (parse-count table s))"
    :fail "(eq r [parse-count table s))"
    :fail "(eq r (parse-count table s)"))

(deftest one-tree
  (are [s pt] (= pt (->> (parse-tree table s) vec-tree))
    "(eq r (parse-count table s))"
      [[:list "(" [:atom "eq"] [:whitespace " "] [:atom "r"] [:whitespace " "] 
         [:list "(" [:atom "parse-count"] [:whitespace " "] [:atom "table"]
           [:whitespace " "] [:atom "s"] ")"] ")"]]
    "[a {b c}(d e)#{f}]"
      [[:vector "[" [:atom "a"] [:whitespace " "] 
         [:map "{" [:atom "b"] [:whitespace " "] [:atom "c"] "}"]
         [:list "(" [:atom "d"] [:whitespace " "] [:atom "e"] ")"]
         [:set "#{" [:atom "f"] "}"]
         "]"]]
      
      ))

