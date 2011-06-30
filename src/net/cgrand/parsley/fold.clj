(ns net.cgrand.parsley.fold
  (:require [net.cgrand.parsley.util :as u]))

(defrecord Anonymous [content])

(defn nodes-vec [^objects nodes]
  (case (alength nodes)
    1 (let [x (aget nodes 0)]
        (if (instance? Anonymous x)
          (recur (.content ^Anonymous x))
          (vec nodes)))
    (if (reduce #(or %1 (anonymous? %2)) false nodes)
      (persistent! 
        (reduce (fn this [v n] 
                  (if (instance? Anonymous n) 
                    (reduce this v (:content n))
                    (conj! v n)))
                (transient []) nodes))
      (vec nodes))))

(defrecord Node [tag content])

(defn make-node [tag children]
  (if tag
    (Node. tag (nodes-vec children))
    (Anonymous. children)))

(defn make-unexpected [s]
  (make-node ::unexpected (to-array [s])))

(defn unexpected? [node] (= (:tag node) ::unexpected))

(defn- tail! [^java.util.ArrayList nodes n]
  (loop [i (unchecked-dec (.size nodes)) to-go (long n)]
    (u/cond
      (unexpected? (.get nodes i))
        (recur (unchecked-dec i) to-go)
      :let [to-go (unchecked-dec to-go)]
      (zero? to-go)
        (let [tail (.subList nodes i (.size nodes))
              r (.toArray tail)]
          (.clear tail)
          r)
      (recur (unchecked-dec i) to-go))))

(defprotocol EphemeralFolding
  (push! [this event]))

(deftype FoldingQueue [^java.util.ArrayList pending ^java.util.ArrayList nodes 
                       ^{:unsynchronized-mutable true, :tag 'long} n]
  EphemeralFolding
  (push! [this event]
    (u/cond
      (unexpected? event) (.add nodes event)
      (not (vector? event))
        (do 
          (.add nodes event)
          (set! n (inc n)))
      :let [[_ N tag] event
            N (long N)]
      (> N n)
        (do
          (doto pending
            (.addAll nodes)
            (.add event))
          (.clear nodes)
          (set! n 0))
      (let [children (tail! nodes N)]
        (.add nodes (make-node tag children))
        (set! n (inc (- n N)))))
    this)
  clojure.lang.IDeref
  (deref [this]
    {:pending (vec pending) :nodes (vec nodes) :n n}))

(defn folding-queue 
  ([] (FoldingQueue. (java.util.ArrayList.) (java.util.ArrayList.) 0))
  ([{:keys [pending nodes n]}] 
    (FoldingQueue. (java.util.ArrayList. ^java.util.Collection pending)
                   (java.util.ArrayList. ^java.util.Collection nodes) n)))

(defn cat [a b]
  (let [fq (folding-queue a)
        fq (reduce push! fq (:pending b))
        fq (reduce push! fq (:nodes b))]
    @fq))

(defn stitchability 
  "Returns :full, or a number (the number of states on A stack which remains untouched)
   when rebasing is possible or nil."
 [a b]
  (u/cond
    :let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
    (= a-end b-start) :full
    :let [[a-stack a-rem] a-end
          [b-stack b-rem] b-start]
    :when (= a-rem b-rem)
    :let [b-tail (subvec b-stack b-watermark)
          n (- (count a-stack) (count b-tail))]
    :when (not (neg? n)) 
    (= b-tail (subvec a-stack n)) n))

(defn rebase [b a]
  (u/cond
    :when-let [st (stitchability a b)] 
    (= :full st) b
    ; if it's not full, it's partial
    :let [[a-end] a
          [b-end b-watermark b-events] b
          [a-stack] a-end
          [b-stack b-rem] b-end
          b-tail (subvec b-stack b-watermark)
          a-stub (subvec a-stack 0 st)]
    [[(into (vec a-stub) b-tail) b-rem] st b-events a-end]))

(defn stitch 
 [a b]
  (when (and a b)
    (let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
      [b-end (min a-watermark b-watermark) (cat a-events b-events) a-start])))
