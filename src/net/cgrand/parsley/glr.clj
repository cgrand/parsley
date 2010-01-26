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

(def empty-rangemap (sorted-map-by compare-ranges))
      
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
  (if (map? (last rhs)) 
    (dec (count rhs))
    (count rhs)))

(defn fix-point [f init]
  (let [v (f init)]
    (if (= v init)
      init
      (recur f v))))

(defn init-state [grammar k]
  (for [rhs (grammar k)] [k (measure rhs) rhs]))

(defn follow [rule] (-> rule (nth 2) first (or {:follow1 [[*min* *max*]]})))

(defn close [init-states state]
  (fix-point (fn [state]
    (let [follows (set (map follow state))]
      (into (set state) (mapcat init-states follows)))) state))

(defn- assoc-multi [map k val]
  (assoc map k (conj (map k #{}) val)))

(defn transitions [close tags state]
  (let [close-transitions #(into % (for [[k state] %] [k (close state)]))
        shift-prods (filter (comp set? follow) state)
        shifts (-> (rmap (for [[k n [terminal & etc]] shift-prods 
                               :let [p #{[k n etc]}], r terminal]
                           [r p]))
                 compact-rangemap close-transitions)
        goto-prods (filter (comp keyword? follow) state)
        gotos (close-transitions
                (reduce (fn [gotos [k n [non-terminal & etc]]]
                          (assoc-multi gotos non-terminal [k n etc])) 
                     {} goto-prods))
        reduce-prods (filter (comp map? follow) state)
        reduces (-> (for [[k n :as prod] reduce-prods
                          :let [{follow-set :follow1} (follow prod)]
                          char-range follow-set] 
                        [char-range #{[k (tags k) n]}])
                  rmap compact-rangemap)]
    [shifts reduces gotos]))

(defn- to-states [[shifts _ gotos]]
  (concat (vals shifts) (vals gotos)))
     
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
  (let [[sym tag n] action
        stack (popN stack n)
        gotos (-> table (get (peek stack)) (nth 2))
        new-state (get gotos sym)
        stack (conj stack new-state)]
    (if (>= (count data) n)
      [stack unreducible-data (conj (popN data n) (make-node tag (peekN data n)))] 
      [stack (-> unreducible-data (into data) (conj (cons :reduce action))) []])))

(defn step1 [stacks table c]
  (let [crange (one (int c))]
    (set
      (mapcat
        (fn single-step1 [[stack :as stack+data]]
          (when-let [[shifts reduces] (table (peek stack))]
            (let [reds (mapcat #(single-step1 (reduce-prod stack+data % table))
                         (reduces crange))]
              (if-let [next-state (shifts crange)]
                (cons (shift stack+data c next-state) reds)
                reds))))
        stacks))))

(defn step [stack table s]
  (reduce #(step1 %1 table %2) stack s)) 

(defn reset [stacks] (map (fn [[stack]] [stack [] []]) stacks))



(comment
(def g {:S #{[:E $]}, 
        :E #{[:E (ranges \* \+) :B] 
             [:B]},
        :B #{[(ranges [\0 \9])]}})
(def table (lr-table g :S #{:S :B}))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "1+2") (step ttable "+3+4") (step1 ttable -1) 
  (->> (map (comp (partial apply str) e/emit* first #(nth % 2)))))
("<B>1</B>+<B>2</B>+<B>3</B>+<B>4</B>")

;; ambiguous 
(def g {:S #{[:E $]}, 
        :E #{[:E (ranges \* \+) :E] 
             [:B]},
        :B #{[(ranges [\0 \9])]}})
(def table (lr-table g :S #{:S :E}))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "1+2") (step ttable "+3+4") (step1 ttable -1) 
  (->> (map (comp (partial apply str) e/emit* first #(nth % 2)))))

("<E><E><E><E>1</E>+<E>2</E></E>+<E>3</E></E>+<E>4</E></E>" 
 "<E><E>1</E>+<E><E><E>2</E>+<E>3</E></E>+<E>4</E></E></E>" 
 "<E><E>1</E>+<E><E>2</E>+<E><E>3</E>+<E>4</E></E></E></E>" 
 "<E><E><E>1</E>+<E><E>2</E>+<E>3</E></E></E>+<E>4</E></E>" 
 "<E><E><E>1</E>+<E>2</E></E>+<E><E>3</E>+<E>4</E></E></E>")
 
;; without follow restrictions 
(def g {:S #{[:E $]},
        :E #{[:A :AB]} 
        :A #{[(ranges \a) :A] 
             [(ranges \a)]},
        :AB #{[:AB (ranges \a \b)]
              [(ranges \a \b)]}})
(def table (lr-table g :S identity))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "aab") (step1 ttable -1) 
  (->> (map (comp (partial apply str) e/emit* first #(nth % 2)))))
("<E><A>a<A>a</A></A><AB>b</AB></E>" "<E><A>a</A><AB><AB>a</AB>b</AB></E>")

;; with follow(1) restrictions 
(def g {:S #{[:E $]},
        :E #{[:A :AB]} 
        :A #{[(ranges \a) :A] 
             [(ranges \a) {:follow1 (ranges \b)}]},
        :AB #{[:AB (ranges \a \b)]
              [(ranges \a \b)]}})
(def table (lr-table g :S identity))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "aab") (step1 ttable -1) 
  (->> (map (comp (partial apply str) e/emit* first #(nth % 2)))))
("<E><A>a<A>a</A></A><AB>b</AB></E>")
 
 
)

