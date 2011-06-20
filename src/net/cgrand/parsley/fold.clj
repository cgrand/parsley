(ns net.cgrand.parsley.fold
  (:require [net.cgrand.parsley.util :as u]))

(defn- anonymous? [x] (and (map? x) (nil? (:tag x))))

(defn nodes-vec [nodes]
  (reduce (fn [vecs n] (if (anonymous? n) 
                         (into vecs (:content n)) 
                         (conj vecs n))) [] nodes))

(defn make-node [tag children]
  (if tag 
    {:tag tag :content (nodes-vec children)}
    {:tag nil :content (nodes-vec children)}))

(defn make-unexpected [s]
  {:tag ::unexpected :content [s]})

(defprotocol Folding
  (pending-events [fs] "Returns a collection of pending events")
  (nodes [fs] "Returns a collection of nodes (incl. unexpected input).")
  (nodes-count [fs] "Returns the number of regular nodes on the complete stack.")
  (cat [fs another-fs]))

(defn unexpected? [node] (= (:tag node) ::unexpected))

(defn- tail [complete n]
  (loop [i (dec (count complete)) to-go n]
    (u/cond
      (unexpected? (nth complete i))
        (recur (dec i) to-go)
      :let [to-go (dec to-go)]
      (zero? to-go)
        (subvec complete i)
      (recur (dec i) to-go))))

(declare empty-folding-queue)

(deftype FoldingQueue [pending complete ncnt]
  Folding
  (pending-events [fs] pending)
  (nodes [fs] complete)
  (nodes-count [fs] ncnt)
  (cat [this fs]
    (if (satisfies? Folding fs)
      (let [that (reduce conj this (pending-events fs))]
        (FoldingQueue. (pending-events that) 
                       (into (nodes that) (nodes fs))
                       (+ (nodes-count that) (nodes-count fs))))
      (into this fs)))
  clojure.lang.Sequential
  clojure.lang.IPersistentCollection
  (count [this]
    (+ (count pending) (count complete)))
  (cons [this event]
    (u/cond
      (unexpected? event)
        (FoldingQueue. pending (conj complete event) ncnt)
      (not (vector? event))
        (FoldingQueue. pending (conj complete event) (inc ncnt))
      :let [[_ N tag] event]
      (> N ncnt)
        (FoldingQueue. (concat pending complete [event]) [] 0)
      :let [children (tail complete N)
            complete (subvec complete 0 (- (count complete) (count children)))
            complete (conj complete (make-node tag children))]
      (FoldingQueue. pending complete (inc (- ncnt N)))))
  (empty [this]
    empty-folding-queue)
  (equiv [this that]
    (boolean (and (satisfies? Folding that) (= pending (pending-events that))
                  (= complete (nodes that)))))
  clojure.lang.Seqable
  (seq [this]
    (seq (concat pending complete)))
  Object
  (hashCode [this]
    (hash-combine (hash pending) complete))
  (equals [this that]
    (boolean (and (satisfies? Folding that) (.equals pending (pending-events that))
                  (.equals complete (nodes that))))))

(def empty-folding-queue (FoldingQueue. nil [] 0))

(defmethod print-method FoldingQueue [fq, ^java.io.Writer w]
  (.write w "#<FoldingQueue ")
  (.write w (pr-str (seq fq)))
  (.write w ">"))

(defn stitchability 
  "Returns :full, or a number (the number of states on A stack which remains untouched)
   when rebasing is possible or nil."
 [a b]
  (u/cond
    :let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
    (= a-end b-start) :full
    :let [[a-stack a-rem] a-end
          [b-stack b-rem] b-start
          b-tail (subvec b-stack b-watermark)
          n (- (count a-stack) (count b-tail))
          a-tail (when-not (neg? n) (subvec a-stack n))]
    (and a-tail (= a-rem b-rem) (= b-tail a-tail))
      n))

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
          watermark st
          a-stub (subvec a-stack 0 watermark)]
    [[(into (vec a-stub) b-tail) b-rem] watermark b-events a-end]))

(defn stitch 
 [a b]
  (when (and a b)
    (let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
      [b-end (min a-watermark b-watermark) (cat a-events b-events) a-start])))
