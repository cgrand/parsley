(ns net.cgrand.parsley.range-map
  (:refer-clojure :exclude [assoc get dissoc])
  (:require [clojure.core :as c]))

(defn compare-range [[i j] [k l]]
  (cond
    (<= j k) -1
    (<= l i) 1
    :else 0))

(defn get 
 ([range-map k]
  (range-map [k k] nil))
 ([range-map k not-found]
  (range-map [k k] not-found)))

(defn overlap [range-map i j]
  (let [i [i i] j [j j]]
    [(find range-map i)
     (subseq range-map > i < j)
     (find range-map j)]))

(defn assoc [range-map [from to :as range] value]
  (let [[a bs c] (apply overlap range-map range)
        range-map (reduce (fn [range-map [k v]]
                            (c/assoc range-map k (conj v value))) 
                    range-map bs)
        range-map (if-let [[[from-a to-a :as k] v] a]
                    (if (< from-a from)
                      (-> range-map (c/dissoc k) (c/assoc [from-a from] v)
                        (c/assoc [from to-a] (conj v value)))
                      (-> range-map (c/assoc k (conj v value))))
                    range-map)
        range-map (if-let [[[from-c to-c :as k] v] c]
                    (if (< to to-c)
                      (-> range-map (c/dissoc k) (c/assoc [to to-c] v)
                        (c/assoc [from-c to] (conj v value)))
                      (-> range-map (c/assoc k (conj v value))))
                    range-map)
        ranges (concat [(if a (key a) [nil from])] 
                 (map key bs) 
                 [(if c (key c) [to nil])])
        spaces (map (fn [[_ to] [from]] [to from]) 
                 ranges (rest ranges))
        singleton #{value}] 
  (reduce #(if (apply < %2)
             (c/assoc %1 %2 singleton) 
             %1) range-map spaces)))

(defn dissoc [range-map [from to :as range] value]
  (let [[a bs c] (apply overlap range-map range)
        range-map (reduce (fn [range-map [k v]]
                            (c/assoc range-map k (disj v value))) 
                    range-map bs)
        range-map (if-let [[[from-a to-a :as k] v] a]
                    (if (< from-a from)
                      (-> range-map (c/dissoc k) (c/assoc [from-a from] v)
                        (c/assoc [from to-a] (disj v value)))
                      (-> range-map (c/assoc k (disj v value))))
                    range-map)
        range-map (if-let [[[from-c to-c :as k] v] c]
                    (if (< to to-c)
                      (-> range-map (c/dissoc k) (c/assoc [to to-c] v)
                        (c/assoc [from-c to] (disj v value)))
                      (-> range-map (c/assoc k (disj v value))))
                    range-map)] 
    range-map))

(defn range-map [& keyvals]
  (reduce #(apply assoc %1 %2) (sorted-map-by compare-range) (partition 2 keyvals)))
