(ns net.cgrand.parsley.tree)

(defprotocol Node
  (len [node])
  (left-cut [node offset])
  (right-cut [node offset]))

(defmacro condl [& clauses]
  (when-let [[test expr & clauses] (seq clauses)]
    (if (= :let test)
      `(let ~expr (condl ~@clauses))
      `(if ~test ~expr (condl ~@clauses)))))

(deftype InnerNode [length a b c]
  Node
  (left-cut [this offset]
    (condl
      :let [la (len a)]
      (<= offset la) (conj (left-cut a offset) nil)
      :let [offset (- offset la)
            lb (len b)]
      (<= offset lb) (conj (left-cut b offset) [a])
      :else (conj (left-cut c offset) [a b])))
  (right-cut [this offset]
    (condl
      :let [la (len a)]
      (< offset la) (conj (right-cut a offset) (if c [b c] [b]))
      :let [offset (- offset la)
            lb (len b)]
      (< offset lb) (conj (right-cut b offset) (when c [c]))
      :else (conj (right-cut c offset) nil)))
  (len [this]
    length))

(defn node [children]
  (let [[a b c] children]
    (InnerNode. (+ (len a) (len b) (if c (len c) 0)) a b c)))

(deftype Leaf [s]
  Node
  (left-cut [this offset]
    [(subs s 0 offset)])
  (right-cut [this offset]
    [(subs s offset)])
  (len [this]
    (count s)))

(defn leaf [s]
  (Leaf. s))

(def E (leaf ""))

(defn group [nodes]
  (if (odd? (count nodes))
    (cons (node (take 3 nodes))
          (map node (partition 2 (drop 3 nodes))))
    (map node (partition 2 nodes))))

(defn chunkify [^String s] (.split s "(?<=\n)"))

(defn edit [tree offset length s]
  (let [[sl & lefts] (left-cut tree offset)
        [sr & rights] (right-cut tree (+ offset length))
        s (str sl s sr)
        leaves (map leaf (chunkify s))]
    (loop [[l & lefts] lefts [r & rights] rights nodes leaves]
      (let [nodes (concat l nodes r)]
        (if (next nodes)
          (recur lefts rights (group nodes))
          (first nodes))))))

(defprotocol Treeable
  (tree [treeable]))

(extend-protocol Treeable
  Leaf
  (tree [leaf] (.s leaf))
  InnerNode
  (tree [nv] (map tree (if (.c nv) [(.a nv) (.b nv) (.c nv)] [(.a nv) (.b nv)]))))

(comment
  => (-> E (splice 0 0 "a\nb") (splice 1 0 "c") tree)
  ("ac\n" "b")
  => (-> E (splice 0 0 "a\nb") (splice 1 0 "cd") tree)
  ("acd\n" "b")
  => (-> E (splice 0 0 "a\nb") (splice 1 0 "cd")  (splice 2 0 "\n\n") tree)
  (("ac\n" "\n") ("d\n" "b")))