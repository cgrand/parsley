;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley
  "An experimental undocumented parser lib/DSL."
  (:require [net.cgrand.parsley.internal :as core]))

;; Parsley can parse ambiguous grammars and thus returns several results.
;; no support for left recursion (yet)

;; reducer: partial-result * event -> partial-result
;; seed: partial-result
;; stitch: partial-result * partial-result -> partial-result
;; partial-result, seed and stitch must define a monoid
(defn parser [cont seed reducer stitch result]
  (with-meta [[nil seed cont]] 
    {::seed seed 
     ::reducer #(if (= "" %2) %1 (reducer %1 %2)) 
     ::stitch stitch
     ::result result}))

(defn step 
 [states s]
  (let [{f ::reducer :as m} (meta states)]
    (with-meta (core/interpreter-step f states s) m)))
      
(defn cut [states]
  (let [m (meta states)
        seed (::seed m)]
    (with-meta (map (fn [[_ _ cont]] [cont seed cont]) states) m)))

(defn- group-reduce 
 [k f seed coll]
  (persistent! (reduce #(let [key (k %2)]
                          (assoc! %1 key (f (%1 key seed) %2)))
                 (transient {}) coll)))

(defn- stitch* [stitch1 states-a states-b]
  (let [states-b-by-k (group-reduce first conj #{} states-b)]
    (mapcat (fn [[k a cont-a]]
              (for [[_ b cont] (states-b-by-k cont-a)] [k (stitch1 a b) cont])) 
      states-a)))
              
(defn stitch [a b]
  (let [m (meta a)
        stitch1 (::stitch m)]
    (with-meta (stitch* stitch1 a b) m))) 

(defn stitchable? [a b]
  (let [b-keys (set (map first b))]
    (every? #(contains? b-keys (% 2)) a))) 

(defn results [states]
  (let [{result ::result} (meta states)]
    (distinct (for [[_ r cont] states :when (empty? cont)] (result r))))) 

;;;; Tree 
(def tree-seed [[] []])

(defn- alter-top [stack f & args]
  (if (seq stack)
    (conj (pop stack) (apply f (peek stack) args))
    stack))

(defn- push-string [stack s]
  (if (string? (peek stack))
    (conj (pop stack) (str (peek stack) s))
    (conj stack s)))

(defn- element [class contents]
  {:tag class :content contents 
   :length (reduce #(+ %1 (or (:length %2) (count %2))) 0 contents)}) 

(defn tree-reducer [[events stack] event]
  (cond
    (= (first event) :start-span)
      [events (conj stack [])]
    (seq stack)
      (cond 
        (string? event)
          [events (alter-top stack push-string event)]
        (map? event)
          [events (alter-top stack conj event)]
        (= (first event) :end-span)
          (let [elt (element (second event) (peek stack))
                etc (pop stack)]
            (if (seq etc)
              [events (alter-top etc conj elt)]
              [(conj events elt) etc])))
    :else
      [(conj events event) stack]))

(defn tree-stitch [a [events-b stack-b]]
  (let [[events stack] (reduce tree-reducer a events-b)]
    [events (into stack stack-b)]))

(defn tree-result [[events stack]]
  events)

    
;; DSL support starts here

;; compile-spec turns a sugar-heavy grammar in nested [f & args]  
(defmulti #^{:private true} compile-spec type)

;; a vector denotes a sequence, supports postfix operators + ? and *
(defmethod compile-spec clojure.lang.IPersistentVector [v]
  `(spaced-cat ~@v))

;; a set denotes an alternative
(defmethod compile-spec clojure.lang.IPersistentSet [s]
  `(alt ~@s))

;; a map denotes a character set
(defmethod compile-spec clojure.lang.IPersistentMap [m]
  `(crange ~@(apply concat m)))

;; a terminal is a String
(defmethod compile-spec String [word]
  `(terminal ~word))

(defmethod compile-spec Character [c]
  `(terminal ~(str c)))

;; a ref to another rule: add support for + ? or * suffixes
(defmethod compile-spec clojure.lang.Keyword [kw]
  (if-let [[_ base suffix] (re-matches #"(.*?)([+*?]\??)" (name kw))]
    (compile-spec
      [(keyword base) (symbol suffix)])
      [:rule kw]))

;; else pass through
(defmethod compile-spec :default [x]
  x)

(defmacro spec [x]
  (compile-spec x))



(defn compile-cat
 "Compile a sequence." 
 [specs]
  (reduce #(condp = %2 
             '*? (conj (pop %1) `(zero-or-more* ~(peek %1)))
             '+? (conj (pop %1) `(one-or-more* ~(peek %1)))
             '?? (conj (pop %1) `(alt* ~(peek %1) pass))
             '* (conj (pop %1) `(greedy-zero-or-more* ~(peek %1)))
             '+ (conj (pop %1) `(greedy-one-or-more* ~(peek %1)))
             '? (conj (pop %1) `(alt* ~(peek %1) (but* ~(peek %1))))
             (conj %1 (compile-spec %2))) [] specs))

(defn- inline-same-ops [op ops]
  (let [xs (mapcat (fn [[o & etc :as x]] (if (= op o) etc [x])) ops)]
    (if (= 1 (count xs))
      (first xs)
      (cons op xs))))

(defn cat* [& ops]
  (inline-same-ops core/op-cat ops))

(defmacro cat [& forms]
  `(cat* ~@(compile-cat forms)))

(defn spaced-cat* [& ops]
  (inline-same-ops :spaced-cat ops))   

(defmacro spaced-cat [& forms]
  `(spaced-cat* ~@(compile-cat forms)))   

(defn zero-or-more* [op]
  [core/op-repeat op])
  
(defmacro zero-or-more [form]
  `(zero-or-more* (spec ~form))) 

(defn one-or-more* [op]
  [:one-or-more op])
  
(defmacro one-or-more [form]
  `(one-or-more* (spec ~form))) 

(defn alt* [& ops]
  (inline-same-ops core/op-alt ops))   

(defmacro alt [& forms]
  `(alt* ~@(map compile-spec forms)))

(defn but* [& ops]
  (cons core/op-negative-lookahead ops))
  
(defmacro but [& forms] 
  `(but* (alt ~@forms)))

(defmacro ?! [& forms]
  `(but ~@forms))

(defn with* [& ops]
  (cons core/op-lookahead ops))

(defmacro with [& forms]
  `(with* ~@(map compile-spec forms)))

(defmacro ?= [& forms]
  `(with ~@forms))


(defn crange [& chars]
  (let [cset (apply sorted-map (map int chars))]
    [core/char-range-op cset]))

(defn- cset [xs]
  (letfn [(ranges [x] 
            (if (map? x)
              (for [[k v] x] [(int k) (int v)])
                (map #(let [i (int %)] [i i]) (str x))))]
    (into (sorted-map) (mapcat ranges  xs))))

(defn- complement-cset [cset]
  (into (sorted-map)
    (map vector 
      (cons 0 (map inc (vals cset))) 
      (concat (map dec (keys cset)) [Integer/MAX_VALUE]))))

(defn one-of [& xs]
  [core/char-range-op (cset xs)])
    
(defn not-one-of [& xs]
  [core/char-range-op (-> xs cset complement-cset)])
    
(def any-char (not-one-of))

(def eof [core/op-eof])

(defn terminal [s]
  [core/op-string s])

(defn token* [op]
  [:token op])

(defmacro token [& forms]
  `(token* (cat ~@forms)))

(defn events [& evts]
  [core/op-events evts])

(def pass (cat))

(defn greedy-zero-or-more* [op]
  [:greedy-zero-or-more op])
  
(defmacro greedy-zero-or-more [form]
  `(greedy-zero-or-more* (spec ~form))) 

(defn greedy-one-or-more* [op]
  [:greedy-one-or-more op])
  
(defmacro greedy-one-or-more [form]
  `(greedy-one-or-more* (spec ~form))) 



(defmulti normalize
 "Adds intersticial space and remove synthetic ops." 
  (fn [_ [op]] 
    (if (#{core/op-alt core/op-cat core/op-lookahead core/op-negative-lookahead} op)
      :composite
      op)))

(defmethod normalize :composite [opts [op & ops]]
  (cons op (map (partial normalize opts) ops)))

(defmethod normalize :spaced-cat [{space :space :as opts} [_ & ops]]
  (let [ops (map (partial normalize opts) ops)]
    (apply cat* (if space (interpose space ops) ops))))

(defmethod normalize :rule [{rules :rules} [_ kw]]
  [core/op-ref (rules kw)])

(defmethod normalize core/op-repeat [{space :space :as opts} [op repeated-op]]
  (let [repeated-op (normalize opts repeated-op)]
    (if space
      (alt* (cat* repeated-op (zero-or-more* (cat* space repeated-op))) pass)
      [op repeated-op]))) 

(defmethod normalize :greedy-zero-or-more [{space :space :as opts} [_ repeated-op]]
  (alt* (but* (normalize opts repeated-op))
    (normalize opts [:greedy-one-or-more repeated-op]))) 

(defmethod normalize :one-or-more [{space :space :as opts} [_ repeated-op]]
  (let [repeated-op (normalize opts repeated-op)]
    (cat* repeated-op 
      (zero-or-more*  (if space (cat* space repeated-op) repeated-op))))) 

(defmethod normalize :greedy-one-or-more [{space :space :as opts} [_ repeated-op]]
  (let [repeated-op (normalize opts repeated-op)
        spaced-op (if space (cat* space repeated-op) repeated-op)]
    (cat* repeated-op 
      (zero-or-more* spaced-op) (but* spaced-op)))) 

(defmethod normalize :token [opts [_ op]]
  (normalize (dissoc opts :space) op)) 

(defmethod normalize :default [opts op]
  op)




(defmacro span [name & ops]
  `(cat (events [:start-span ~name]) ~@ops (events [:end-span ~name])))   

(defn- keywordize [sym] (-> sym name keyword))

(defn- private? [kw]
  (.endsWith (name kw) "-"))

(defmacro grammar [options-map & rules]
  (let [[options-map rules] (if (map? options-map) 
                              [options-map rules]
                              [{} (cons options-map rules)])
        {:keys [main seed reducer stitch result] 
         :or {main (first rules) 
              seed `tree-seed 
              reducer `tree-reducer 
              stitch `tree-stitch
              result `tree-result}} options-map 
        rules (partition 2 rules)
        rules-names (map (comp second 
                           (partial re-matches #"(.*?)-?") name first) rules)
        atom-names (map gensym rules-names)
        bodies (for [[kw rule] rules] 
                 (if (private? kw) `(spec ~rule) `(span ~kw ~rule)))
        space-spec (if-let [space (options-map :space)] `(cat ~space ~'*) `(cat))]
   `(let [~@(interleave atom-names (repeat `(atom nil)))
          opts# {:rules ~(zipmap (map keyword rules-names) atom-names)}
          space-op# (normalize opts# (spec ~space-spec))
          opts# (assoc opts# :space space-op#)
          main-op# (cat* space-op# (normalize opts# (spec ~main)) space-op#)
          ops# ~(zipmap atom-names bodies)]
      (doseq [[a# op#] ops#]
        (reset! a# (normalize opts# op#)))
      (parser [main-op#] ~seed ~reducer ~stitch ~result))))
