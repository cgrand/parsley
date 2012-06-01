(ns net.cgrand.parsley.views
  "Views on functional trees."
  (:require [clojure.zip :as z]))

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
;; Alternative impls could be defrecord+memoization or using WeakReferences

(defn fleaf 
  "Constructs a functional leaf."
  [s]
  (memoize (fn [leaf node]
             (leaf s))))

(defn fnode 
  "Constructs a functional node." [tag content]
  (memoize (fn [leaf node]
             (node tag content))))

(defn view 
  "Creates a simple recursive view function. The leaf function is passed
   the string stored into a leaf and the node function gets the tag and
   the sequence of valus returned by the viesw recursively called on the
   children nodes."
  [leaf node]
  (letfn [(node* [tag fs]
            (node tag (map v fs)))
          (v [f]
            (f leaf node*))]
    v))

(defn nonrec-view 
  "Creates a view function. Unlike view, the second arg passed to node is a
   collection of children functional trees." 
  [leaf node]
  (fn [f] (f leaf node)))

(defn content 
  "View that returns the nodes (or nil) of a functional tree."
  [f]
  (f (constantly nil) (fn [_ fs] fs)))

(defn tag 
  "View that returns the tag (or nil) of a functional tree."
  [f]
  (f (constantly nil) (fn [tag _] tag)))

(def text
  (view identity #(apply str %2)))


(def length
  (view count #(reduce + %2)))

(def offsets 
  (nonrec-view (constantly nil)
               (fn [_ nodes]
                 (into (sorted-map) (next (reductions 
                                            (fn [[offset _] node]
                                              [(+ offset (length node)) node])
                                            [0 nil]
                                            nodes))))))

;; zipper on functional trees
(defn fzip [root]
  (z/zipper content content (fn [node children]
                              (fnode (tag node) (vec children)))))

;; we need indexed/measured zippers!
(defn offset-at
  "Returns the offset at the *start* of the node pointed by the loc. "
  [loc]
  (if-let [ploc (z/up loc)]
    (let [roffsets (offsets (z/node ploc))
          n (count (z/lefts loc))
          roffset (if (zero? n) 0 (key (first (drop (dec n) roffsets))))]
      (+ roffset (offset-at ploc)))
    0))

(defn path-to [node offset]
  (loop [node node offset offset path []]
    (if-let [offsets (offsets node)]
      (let [[o n] (first (subseq offsets >= offset))
            so (- o (length n))
            ro (- offset so)]
        (recur n ro (conj path [node offset])))
      (conj path [node offset]))))

#_(defn loc-at [loc offset]
  (if (and (z/branch? loc) (seq (z/children loc)))
    (let [cloc (z/down loc)
          lefts (subseq (offsets loc) < offset)])
    )
  )
