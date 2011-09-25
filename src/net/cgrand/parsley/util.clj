(ns net.cgrand.parsley.util
  "Some functions and a collection of variations on Clojure's core macros. 
   Let's see which features end up being useful."
  {:author "Christophe Grand"}
  (:refer-clojure :exclude [cond when-let if-let]))

(defmacro if-let
  "A variation on if-let where all the exprs in the bindings vector must be true.
   Also supports :let."
  ([bindings then]
    `(if-let ~bindings ~then nil))
  ([bindings then else]
    (if (seq bindings)
      (if (= :let (bindings 0))
        `(let ~(bindings 1)
           (if-let ~(subvec bindings 2) ~then ~else))
        `(let [test# ~(bindings 1)]
           (if test#
             (let [~(bindings 0) test#]
               (if-let ~(subvec bindings 2) ~then ~else))
             ~else)))
      then)))

(defmacro when-let
  "A variation on when-let where all the exprs in the bindings vector must be true.
   Also supports :let."
  [bindings & body]
  `(if-let ~bindings (do ~@body)))

(defmacro cond 
  "A variation on cond which sports let bindings and implicit else:
     (cond 
       (odd? a) 1
       :let [a (quot a 2)]
       (odd? a) 2
       3).
   Also supports :when-let and binding vectors as test expressions." 
  [& clauses]
  (when-let [[test expr & more-clauses] (seq clauses)]
    (if (next clauses)
      (if-let [sym ({:let `let :when `when :when-let `when-let} test)]
        (list sym expr `(cond ~@more-clauses))
        (if (vector? test)
          `(if-let ~test ~expr (cond ~@more-clauses))
          `(if ~test ~expr (cond ~@more-clauses))))
      test)))

(comment ;if one could define cond with itself it would read:
  (cond
    :when-let [[test expr & more-clauses] (seq clauses)]
    (not (next clauses)) test
    [sym ({:let `let :when `when :when-let `when-let} test)]
      (list sym expr `(cond ~@more-clauses))
    (vector? test)
      `(if-let ~test ~expr (cond ~@more-clauses))
    `(if ~test ~expr (cond ~@more-clauses))))

(defn map-vals [map f]
  (into map (for [[k v] map] [k (f k v)])))

(defn fix-point [f init]
  (let [v (f init)]
    (if (= v init)
      init
      (recur f v))))


