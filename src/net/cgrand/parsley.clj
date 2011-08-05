;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley
  "A total truly incremental parser generator. Grammars are expressed 
   in a value-based DSL."
  (:require [net.cgrand.parsley.lrplus :as core]
            [net.cgrand.parsley.fold :as f]
            [net.cgrand.parsley.tree :as t]
            [net.cgrand.parsley.util :as u]
            [net.cgrand.parsley.grammar :as g]))


(defrecord Node [tag content]) ; for memory efficiency

(defn- stepper [table options-map]
  (let [options-map (merge
              {:make-node #(Node. %1 %2) 
               :make-leaf nil} ; nil for identity
              options-map)
        options-map (if-not (:make-unexpected options-map)
                      (let [make-node (:make-node options-map)] 
                        (assoc options-map :make-unexpected #(make-node ::unexpected [%])))
                      options-map)
        ops (select-keys options-map [:make-node :make-leaf :make-unexpected])]
    ^{::options options-map} ; feeling dirty, metadata make me uneasy
    (fn self
      ([s]
        (let [a (self core/zero s) b (self a nil)]
          (-> (f/stitch a b) (nth 2) f/finish)))
      ([state s]
        (core/step table ops state s)))))

(defn make-parser [options-map rules]
  (-> (apply g/grammar options-map rules) core/lr-table core/totalize 
    core/number-states (stepper options-map)))

(defn parser [options-map & rules]
  (let [[options-map rules] (if-not (map? options-map)
                              [{} (cons options-map rules)]
                              [options-map rules])]
    (make-parser options-map rules)))

(defn unspaced 
 "Creates an unspaced sequence." 
 [& specs]
  (apply g/unspaced specs))


(defn- memoize-parser [f]
  (let [cache (atom nil)]
    (fn [input]
      (u/cond
        [last-result @cache
         new-result (f/rebase last-result input)]
          (if (identical? last-result new-result)
            last-result
            (reset! cache new-result))
        (reset! cache (f input))))))

(defn- memoize1 [parser s]
  (memoize-parser #(parser % s)))

(defn- memoize2 [mpa mpb]
  (memoize-parser #(let [a (mpa %)
                         b (mpb a)]
                     (f/stitch a b))))

(defn- memoize-1shot [f]
  (let [cache (atom [(Object.) nil])]
    (fn [& args]
      (let [[cargs cr] @cache]
        (if (= args cargs)
          cr
          (let [r (apply f args)]
            (reset! cache [args r])
            r))))))

(defn- memoize-eof [parser]
  (let [mp (memoize1 parser nil)]
    (memoize-1shot #(-> (f/stitch % (mp %)) (nth 2) f/finish))))

(defn incremental-buffer
  "Creates an empty incremental buffer for the specified parser." 
  [parser]
	  {:buffer (t/buffer {:unit #(memoize1 parser %) 
                       :plus memoize2 
                       :chunk #(.split ^String % "(?<=\n)")
                       :left #(subs %1 0 %2) 
                       :right subs 
                       :cat str})
    :eof-parser (memoize-eof parser)
    :options (::options (meta parser))})

(defn edit 
  "Returns a new buffer reflecting the specified edit."
  [incremental-buffer offset length s]
  (update-in incremental-buffer [:buffer] t/edit offset length s))

(defn parse-tree 
  "Returns the parse-tree."
  [incremental-buffer]
  (let [f (t/value (:buffer incremental-buffer))
        a (f core/zero)]
    ((:eof-parser incremental-buffer) a))) 

