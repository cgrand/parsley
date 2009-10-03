;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.shell
 "Low level API"
  (:require [net.cgrand.parsley.core :as core]))

;; reducer: partial-result * event -> partial-result
;; seed: partial-result
;; stitch: partial-result * partial-result -> partial-result
;; partial-result, seed and stitch must define a monoid
(defn parser [cont seed reducer stitch]
  (with-meta [[nil seed cont]] 
    {::seed seed 
     ::reducer #(if (= "" %2) %1 (reducer %1 %2)) 
     ::stitch stitch}))

(defn- step* 
 [states s]
  (let [{f ::reducer :as m} (meta states)]
    (with-meta (distinct (core/interpreter-step f states s)) m)))
      
(defn step 
 [states s]
  (step* states (or s ""))) 
      
(defn eof [states]
  (step* states nil))
  
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
  (for [[_ result cont] states :when (empty? cont)] result)) 

