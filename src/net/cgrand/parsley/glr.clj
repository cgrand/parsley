(ns net.cgrand.parsley.glr)

;; a grammar is a map of keywords to sets of vector of keywords and terminals
;; empty productions are NOT allowed
;; TODO : define what constitues a terminal
;; a terminal is:
;; * a (sorted) set of codepoints ranges (inclusive bounds)

(def *min* Integer/MIN_VALUE)
(def *max* Integer/MAX_VALUE)
(def *eof* -1)

(defn compare-ranges 
 "Compare two disjoint ranges."
 [[la ha] [lb hb]]
  (cond
    (<= ha lb) -1
    (<= hb la) 1
    :else 0))

(def empty-ranges (sorted-set-by compare-ranges))
(def empty-rangemap (sorted-map-by compare-ranges))
      
(defn- gaps [l ranges h]
  (let [boundaries (concat [l]
                     (mapcat (fn [[l h]] [(dec l) (inc h)]) 
                       (subseq ranges >= [l l] <= [h h])) 
                     [h])]
    (for [[l h] (partition 2 boundaries)
          :when (<= l h)] [l h])))
    
(defn complement-ranges [ranges]
  (into empty-ranges (gaps *min* ranges *max*)))

(defn conj-ranges [ranges [l h :as lh]]
  (let [ranges (into ranges (gaps l ranges h))
        ranges (let [[a b :as ab] (ranges [l l])]
                  (if (= a l) 
                    ranges
                    (-> ranges (disj ab) (conj [a (dec l)] [l b]))))
        ranges (let [[a b :as ab] (ranges [h h])]
                  (if (= b h) 
                    ranges
                    (-> ranges (disj ab) (conj [a h] [(inc h) b]))))]
    ranges))

(defn into-ranges 
 ([] empty-ranges)
 ([ranges] ranges)
 ([ranges range]
   (reduce conj-ranges ranges range)) 
 ([ranges range & etc]
   (reduce into-ranges (into-ranges ranges range) etc))) 

(defn ranges [& xs]
  (set (for [x xs] (if (or (char? x) (number? x)) [(int x) (inc (int x))] 
                     (let [[l h] x] [(int l) (inc (int h))])))))

(def $ (ranges *eof*))

(defn- one [n] [n (inc n)])

(defn assoc-rangemap [rangemap [l h] vals]
  (if (and (< l h) (seq vals))
    (let [vals (set vals)
          rangemap (or (when-let [[[ll hl :as low] vs] (find rangemap (one l))]
                         (when (< ll l)
                           (-> rangemap 
                             (dissoc low)
                             (assoc [ll l] vs)
                             (assoc [l hl] vs))))
                     rangemap)
          rangemap (or (when-let [[[lh hh :as high] vs] (find rangemap (one h))]
                         (when (< h hh)
                           (-> rangemap 
                             (dissoc high)
                             (assoc [lh h] vs)
                             (assoc [h hh] vs))))
                     rangemap)
          ranges+vals (subseq rangemap >= (one l) < (one h))
          gaps (partition 2 (concat [l] (mapcat key ranges+vals) [h]))
          rangemap (into rangemap (for [[r vs] ranges+vals] 
                                    [r (into vs vals)])) 
          rangemap (into rangemap (for [[h l :as r] gaps :when (< h l)]
                                    [r vals]))]
      rangemap)
    rangemap))

(defn into-rangemap [rangemap rvs]
  (reduce (partial apply assoc-rangemap) rangemap rvs))
  
(defn rmap [rvs]
  (into-rangemap empty-rangemap rvs))

(defn- compact-rvs [rvs]
  (lazy-seq
    (when-first [[[l h] vs] rvs]
      (loop [h h rvs (next rvs)] 
         (if-let [[[[nl nh] nvs] & etc] (seq rvs)]
           (if (and (= h nl) (= vs nvs))
             (recur nh etc)
             (cons [[l h] vs] (compact-rvs rvs)))
           (cons [[l h] vs] nil))))))

(defn compact-rangemap [rangemap]
  (rmap (compact-rvs rangemap)))



(defn measure [rhs]
  (count rhs))

(defn fix-point [f init]
  (let [v (f init)]
    (if (= v init)
      init
      (recur f v))))

(defn init-state [grammar k]
  (for [rhs (grammar k)] [k (measure rhs) rhs]))

(defn follow [rule] (-> rule (nth 2) first))

(defn close [init-states state]
  (fix-point (fn [state]
    (let [follows (set (map follow state))]
      (into (set state) (mapcat init-states follows)))) state))

(defn- assoc-multi [map k val]
  (assoc map k (conj (map k #{}) val)))

(defn- wrap-vals [f map]
  (into map (for [[k v] map] [k (f v)]))) 

(defn transitions [close tags state]
  (let [close-transitions #(into % (for [[k state] %] [k (close state)]))
        shift-prods (filter (comp set? follow) state)
        shifts (wrap-vals (fn [x] #{[:shift x]})
                 (-> (rmap 
                       (for [[k n [terminal & etc]] shift-prods 
                             :let [p #{[k n etc]}], r terminal]
                         [r p]))
                   compact-rangemap
                   close-transitions))
        goto-prods (filter (comp keyword? follow) state)
        gotos (close-transitions
                (reduce (fn [gotos [k n [non-terminal & etc]]]
                          (assoc-multi gotos non-terminal [k n etc])) 
                     {} goto-prods))
        reduce-prods (filter (comp nil? follow) state)
        reduces (rmap (for [[k n] reduce-prods] 
                        [[*min* *max*] #{[:reduce k (tags k) n]}]))]
    [(into-rangemap shifts reduces) gotos]))

(defn- to-states [[actions-table gotos]]
  (concat (for [actions (vals actions-table), [action state] actions
                :when (= :shift action)]
            state) 
    (vals gotos)))
     
(defn lr-table [grammar start tags]
  (let [init (partial init-state grammar)
        close (partial close init)
        state0 (-> start init close)
        transitions (partial transitions close tags)]
    [(fix-point 
       (fn [table]
         (let [states (mapcat to-states (vals table))
               has-no-transitions? #(when-not (table %) %)] 
           (if-let [state (some has-no-transitions? states)]
             (assoc table state (transitions state))
             table))) {state0 (transitions state0)})
     state0])) 

(defn peekN [stack n]
  (let [s (- (count stack) n)]
    (cond 
      (pos? s) (subvec stack s)
      (zero? s) stack)))

(defn popN [stack n]
  (let [s (- (count stack) n)]
    (cond 
      (pos? s) (subvec stack 0 s)
      (zero? s) [])))

(defn- merge-text [coll]
  (lazy-seq
    (let [[cs xs] (split-with (complement map?) coll)]
      (cond
        (seq cs)
          (cons (apply str cs) (merge-text xs))
        (seq xs)
          (cons (first xs) (merge-text (rest xs))))))) 

(defn make-node [tag nodes]
  (let [content (->> nodes (mapcat #(if (vector? %) % [%])) merge-text vec)]
    (if tag
      {:tag tag :content content}
      content)))

(defn- shift [[stack unreducible-data data :as stack+data] c new-state]
  (if (= *eof* c) 
    stack+data
    [(conj stack new-state) unreducible-data (conj data c)]))

(defn- reduce-prod [[stack unreducible-data data] action table]
  (let [[_ sym tag n] action
        stack (popN stack n)
        new-state (-> table (get (peek stack)) second (get sym))
        stack (conj stack new-state)]
    (if (>= (count data) n)
      [stack unreducible-data (conj (popN data n) (make-node tag (peekN data n)))] 
      [stack (-> unreducible-data (into data) (conj action)) []])))

(defn step1 [[stack :as stack+data] table c]
  (let [state (peek stack)]
    (when-let [[op :as action] 
                 (-> table (get state) first (get (one (int c))) first)]
      (cond
        (= :shift op)
          (shift stack+data c (second action))  
        (= :reduce op)
          (recur (reduce-prod stack+data action table) table c)))))

(defn step [stack table s]
  (reduce #(step1 %1 table %2) stack s)) 

(defn reset [[stack]] [stack [] []])
            
        



(comment
(def g {:S #{[:E $]}, 
        :E #{[:E (ranges \* \+) :B] 
             [:B]},
        :B #{[(ranges [\0 \9])]}})
(def table (lr-table g :S #{:S :B}))
(def ttable (first table))
(def sop [[(second table)] [] []])
(-> sop (step ttable "1+2") (step ttable "+3") (step1 ttable -1) next second first e/emit* (->> (apply str)))
)

