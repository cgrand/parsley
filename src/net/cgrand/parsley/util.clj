(ns net.cgrand.parsley.util
  (:refer-clojure :exclude [cond]))

(defmacro cond 
  "A variation on cond which sports let bindings:
     (cond 
       (odd? a) 1
       :let [a (quot a 2)]
       (odd? a) 2
       :else 3)" 
  [& clauses]
  (when-let [[test expr & clauses] (seq clauses)]
    (if (= :let test)
      `(let ~expr (cond ~@clauses))
      `(if ~test ~expr (cond ~@clauses)))))


