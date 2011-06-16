(ns net.cgrand.parsley.tree)

(defprotocol Node
  (len [node])
  (left-cut [node offset])
  (right-cut [node offset])
  (value [node])
  (ops [node]))

(defrecord Ops [chunkify unit plus])

(defmacro condl [& clauses]
  (when-let [[test expr & clauses] (seq clauses)]
    (if (= :let test)
      `(let ~expr (condl ~@clauses))
      `(if ~test ~expr (condl ~@clauses)))))

(deftype InnerNode [ops val length a b c]
  Node
  (left-cut [this offset]
    (condl
      :let [la (len a)]
      (<= offset la) (conj (left-cut a offset) nil)
      :let [offset (- offset la)
            lb (len b)]
      (<= offset lb) (conj (left-cut b offset) [a])
      :let [offset (- offset lb)]
      :else (conj (left-cut c offset) [a b])))
  (right-cut [this offset]
    (condl
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

(defn group [ops nodes]
  (if (odd? (count nodes))
    (cons (node ops (take 3 nodes))
          (map #(node ops %) (partition 2 (drop 3 nodes))))
    (map #(node ops %) (partition 2 nodes))))

(defn line-chunkify [^String s] (.split s "(?<=\n)"))

(defn edit [tree offset length s]
  (let [[sl & lefts] (left-cut tree offset)
        [sr & rights] (right-cut tree (+ offset length))
        s (str sl s sr)
        ops (ops tree)
        leaves (map #(leaf ops %) ((:chunkify ops) s))]
    (loop [[l & lefts] lefts [r & rights] rights nodes leaves]
      (let [nodes (concat l nodes r)]
        (if (next nodes)
          (recur lefts rights (group ops nodes))
          (first nodes))))))

;; repl stuff

(def str-ops (Ops. line-chunkify identity str))

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