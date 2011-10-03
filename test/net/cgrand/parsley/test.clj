(ns net.cgrand.parsley.test
  (:require [net.cgrand.parsley.lrplus :as core] :reload)
  (:require [net.cgrand.parsley :as p] :reload)
  (:require [net.cgrand.parsley.util :as u])
  (:use clojure.test))

(defn- unexpected? [x]
  (when (and (vector? x) (= ::p/unexpected (first x)))
    (second x)))

(defn v [node]
  (if (map? node)
    (reduce (fn [v x]
              (u/if-let [b (unexpected? x)
                         a (unexpected? (peek v))]
                (conj (pop v) [::p/unexpected (str a b)])
                (conj v x))) 
      [(:tag node)] (map v (:content node)))
    node))

(deftest empty-grammar
  (let [eg (p/parser {:main []})]
    (are [s t] (= (v (eg s)) t)
      "" [::p/root]
      "abcdef" [::p/root [::p/unexpected "abcdef"]]
      "   " [::p/root [::p/unexpected "   "]]
      " a " [::p/root [::p/unexpected " a "]])))

(deftest empty-whitespaced-grammar
  (let [eg (p/parser {:main []
                      :space :ws?
                      :root-tag :root}
             :ws #" +")]
    (are [s t] (= (v (eg s)) t)
      "" [:root]
      "abcdef" [:root [::p/unexpected "abcdef"]]
      "   " [:root [:ws "   "]]
      " a " [:root [:ws " "] [::p/unexpected "a "]])))

(defn sexpr (p/parser {:main :expr*
                         :space :ws?
                         :root-tag :root}
                :ws #"\s+"
                :expr- #{:vector :list :map :set :symbol}
                :symbol #"[a-zA-Z-]+"
                :vector ["[" :expr* "]"]
                :list ["(" :expr* ")"]
                :map ["{" :expr* "}"]
                :set ["#{" :expr* "}"]))

(deftest sexpr-once
  (are [s t] (= (v (sexpr s)) t)
      "" [:root]
      "hello world" [:root [:symbol "hello"] [:ws " "] [:symbol "world"]]
      " hello " [:root [:ws " "] [:symbol "hello"] [:ws " "]]
      "(hello #{world kitty})" [:root [:list "(" [:symbol "hello"] [:ws " "] 
                                       [:set "#{" [:symbol "world"] [:ws " "] 
                                        [:symbol "kitty"] "}"] ")"]]
      "(hello #{world kitty])" [::p/unfinished 
                                [::p/unfinished "(" [:symbol "hello"] [:ws " "] 
                                 [::p/unfinished "#{" [:symbol "world"] [:ws " "] 
                                  [:symbol "kitty"] [::p/unexpected "])"]]]]
      "hello 123 world" [:root [:symbol "hello"] [:ws " "] [::p/unexpected "123 "] 
                         [:symbol "world"]]))