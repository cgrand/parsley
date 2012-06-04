(ns net.cgrand.parsley.views)

; Right now compute is responsible for memoization
(defprotocol ViewableNode
  (compute [n leaf node]
    "Applies either the leaf or node function to the node at hand.
     The leaf function expects one argument: a string.
     The node function expects two arguments: a keyword and a collection of
     children nodes."))

; TODO: make Node and String Viewable + memoization

(defn view 
  "Creates a simple recursive view function. The leaf function is passed
   the string stored into a leaf and the node function gets the tag and
   the sequence of values returned by the view recursively called on the
   children nodes."
  [leaf node]
  (letfn [(node* [tag fs]
            (node tag (map v fs)))
          (v [n]
            (compute n leaf node*))]
    v))

(defn nonrec-view 
  "Creates a view function. Unlike view, the second arg passed to node is a
   collection of children functional trees." 
  [leaf node]
  (fn [n] (compute n leaf node)))

(def content 
  "View that returns the nodes (or nil) of a tree. Unlike :content works on
   all viewable trees"
  (nonrec-view (constantly nil) (fn [_ nodes] nodes)))

(def tag 
  "View that returns the tag (or nil) of a functional tree. Unlike :tag works
   on all viewable trees."
  (nonrec-view (constantly nil) (fn [tag _] tag)))

(def text
  (view identity #(apply str %2)))

(def length
  (view count #(reduce + %2)))

(def offsets
  "View which returns a sorted-map of relative end offsets to children nodes."
  (nonrec-view (constantly nil)
               (fn [_ nodes]
                 (into (sorted-map) (next (reductions 
                                            (fn [[offset _] node]
                                              [(+ offset (length node)) node])
                                            [0 nil]
                                            nodes))))))

;; zipper on viewable trees
#_(defn fzip [root]
  (z/zipper content content (fn [node children]
                              (fnode (tag node) (vec children)))))

;; we need indexed/measured zippers!
#_(defn offset-at
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
