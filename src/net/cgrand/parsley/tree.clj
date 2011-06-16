(ns net.cgrand.parsley.tree
  "An incremental character buffer backed by a 2-3 tree.")

(defprotocol Node
  "Protocol for inner nodes and leaves of a 2-3 buffer.
   The buffer is parametrized by a triple of fns, see the ops method."
  (len [node] "Returns the length of the Node")
  (left-cut [node offset])
  (right-cut [node offset])
  (value [node] "The result value for this node.")
  (ops [node] "Returns a map of fns with keys :unit, :plus and :chunk.
  `unit` turns a String into a value from the result type, 
  `plus` (an associative fn) combines two values from the result type into
    a value of the result type,
  `chunk` which breaks a String into a seq of strings -- it controls the
    computational granularity of the buffer."))

(defrecord Ops [chunk unit plus])

(defmacro cond 
  "A variation on cond which sports let bindings:
     (cond 
       (odd? a) 1
       :let [a (quot a 2]]
       (odd? a) 2
       :else 3)" 
  [& clauses]
  (when-let [[test expr & clauses] (seq clauses)]
    (if (= :let test)
      `(let ~expr (net.cgrand.parsley.tree/cond ~@clauses))
      `(if ~test ~expr (net.cgrand.parsley.tree/cond ~@clauses)))))

(deftype InnerNode [ops val length a b c]
  Node
  (left-cut [this offset]
    (cond
      :let [la (len a)]
      (<= offset la) (conj (left-cut a offset) nil)
      :let [offset (- offset la)
            lb (len b)]
      (<= offset lb) (conj (left-cut b offset) [a])
      :let [offset (- offset lb)]
      :else (conj (left-cut c offset) [a b])))
  (right-cut [this offset]
    (cond
      :let [la (len a)]
      (< offset la) (conj (right-cut a offset) (if c [b c] [b]))
      :let [offset (- offset la)
            lb (len b)]
      (< offset lb) (conj (right-cut b offset) (when c [c]))
      :let [offset (- offset lb)]
      :else (conj (right-cut c offset) nil)))
  (len [this]
    length)
  (value [this] 
    val)
  (ops [this] 
    ops))

(defn node [ops children]
  (let [[a b c] children
        plus (:plus ops)
        val (plus (value a) (value b))
        val (if c (plus val (value c)) val)]
    (InnerNode. ops val (+ (len a) (len b) (if c (len c) 0)) a b c)))

(deftype Leaf [ops val s]
  Node
  (left-cut [this offset]
    [(subs s 0 offset)])
  (right-cut [this offset]
    [(subs s offset)])
  (len [this]
    (count s))
  (value [this] 
    val)
  (ops [this] 
    ops))

(defn leaf [ops s]
  (Leaf. ops ((:unit ops) s) s))

(defn group 
  "Groups a sequence of at least two nodes into a sequence of nodes with 2 or 3 children."
  [nodes]
  (let [ops (:ops (first nodes))]
    (if (odd? (count nodes))
      (cons (node ops (take 3 nodes))
            (map #(node ops %) (partition 2 (drop 3 nodes))))
      (map #(node ops %) (partition 2 nodes)))))

(defn edit 
  "Performs an edit on the buffer. Content from offset to offset+length (excluded) is replaced
   by s." 
  [tree offset length s]
  (let [[sl & lefts] (left-cut tree offset)
        [sr & rights] (right-cut tree (+ offset length))
        s (str sl s sr)
        ops (ops tree)
        leaves (map #(leaf ops %) ((:chunk ops) s))]
    (loop [[l & lefts] lefts [r & rights] rights nodes leaves]
      (let [nodes (concat l nodes r)]
        (if (next nodes)
          (recur lefts rights (group nodes))
          (first nodes))))))

;; repl stuff
(defn line-chunk [^String s] (.split s "(?<=\n)"))

(def str-ops (Ops. line-chunk identity str))

(def E (leaf str-ops ""))

(defprotocol Treeable
  (tree [treeable]))

(extend-protocol Treeable
  Leaf
  (tree [leaf] (.s leaf))
  InnerNode
  (tree [nv] (map tree (if (.c nv) [(.a nv) (.b nv) (.c nv)] [(.a nv) (.b nv)]))))

(comment
  => (-> E (edit 0 0 "a\nb") (edit 1 0 "c") ((juxt tree value)))
  ("ac\n" "b")
  => (-> E (edit 0 0 "a\nb") (edit 1 0 "cd") ((juxt tree value)))
  ("acd\n" "b")
  => (-> E (edit 0 0 "a\nb") (edit 1 0 "cd")  (edit 2 0 "\n\n") ((juxt tree value)))
  (("ac\n" "\n") ("d\n" "b")))