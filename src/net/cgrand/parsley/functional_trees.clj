(ns net.cgrand.parsley.functional-trees
  "Views on functional trees."
  (:require [net.cgrand.parsley.views :as v]))

;; Functional trees are trees-as-functions (a subset of objects-as-functions)
;; A functional tree is a function of two arguments: leaf and node.
;; leaf and node are two functions:
;; * leaf takes one string and returns a value in a view domain,
;; * node takes a tag (keyword) and a collection of children functional trees
;;   and returns a value in the same view domain as leaf's.
;; When a functional tree represent a leaf, leaf is called, when it's a inner
;; node, node is called.
;;
;; The purpose of these functional trees (over maps for example) is that they
;; can be memoizing and the caches are associated with the trees, not with
;; the functions.
;;
;; It's an expedient implementation, better impl welcome.
;;
;; Canonicalizing may be interesting for all keywords, single spaces etc.

(defn fleaf 
  "Constructs a functional leaf."
  [s]
  (memoize (fn [leaf node]
             (leaf s))))

(defn fnode 
  "Constructs a functional node." [tag content]
  (memoize (fn [leaf node]
             (node tag content))))

(extend-type clojure.lang.Fn
  v/ViewableNode
  (compute [f leaf node]
    (f leaf node)))
