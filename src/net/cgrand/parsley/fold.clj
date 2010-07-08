(ns net.cgrand.parsley.fold)

(defn- branch? [x] (and (map? x) (nil? (:tag x))))

(defn nodes-vec [nodes]
  (vec (mapcat #(->> % (tree-seq branch? :content) (remove branch?)) nodes)))

(defn make-node [tag children]
  (if tag 
    {:tag tag :content (nodes-vec children)}
    {:tag nil :content children}))

(defn fold [events]
  (letfn [(fold-nodes [events n]
            (loop [events events folded () n n]
              (cond
                (zero? n)
                  [events folded]
                (empty? events)
                  [(vec folded)]
                :else
                  (let [event (peek events)
                        etc (pop events)]
                    (if-let [[_ N tag] (when (vector? event) event)]
                      (let [[rem children] (fold-nodes etc N)]
                        (if children
                          (recur rem (conj folded (make-node tag children)) 
                            (dec n))
                          [(conj rem event)]))
                      (recur etc (conj folded event) (dec n)))))))]
    (first (fold-nodes events Integer/MAX_VALUE))))

(defn stitch-events [a b]
  (fold (into a b)))

(defn stitchability 
  "Returns :full, :partial or nil."
 [a b]
  (let [[a-end a-watermark a-events a-start] a
        [b-end b-watermark b-events b-start] b]
    (cond
      (= a-end b-start) :full
      (let [[a-stack a-rem] a-end
            [b-stack b-rem] b-start
            b-tail (subvec b-stack b-watermark)
            n (- (count a-stack) (count b-tail))
            a-tail (when-not (neg? n) (subvec a-stack n))]
        (and a-tail (= a-rem b-start) (= b-tail a-tail))) :partial)))


(defn stitch 
 ([a b] (stitch a b make-node))
 ([a b make-node]
  (when (and a b)
    (let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
      (case (stitchability a b)
        :full [b-end (min a-watermark b-watermark) 
               (stitch-events a-events b-events) a-start] 
        #_:partial #_(let [[a-stack] a-end
                       [b-start-stack] b-start
                       watermark (- (count a-stack) 
                                   (- (count b-start-stack) b-watermark)) 
                       stub (subvec a-stack 0 watermark)
                       [b-stack b-rem] b-end
                       tail (subvec b-stack b-watermark)]
                   [[(into stub tail) b-rem] (min a-watermark watermark)
                    (stitch-events make-node a-events b-events) a-start]))))))

(comment
(defn chunk-tree [proj-fns chunks])

(defn edit [chunk-tree i len s] 
  )

(set! *warn-on-reflection* true) 
  )

