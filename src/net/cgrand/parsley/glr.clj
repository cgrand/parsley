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
          rangemap (or (when-let [[[lh hh :as high] vs] (find rangemap (one (dec h)))]
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

(def codepoint int) ; just to remove the hint

(defn ranges [& xs]
  (set (for [x xs] (if (or (char? x) (number? x)) 
                     [(codepoint x) (inc (codepoint x))] 
                     (let [[l h] x] [(codepoint l) (inc (codepoint h))])))))

(defn complement-ranges [s]
  (let [m (-> empty-rangemap
            (assoc-rangemap [*min* *max*] #{:a})
            (into-rangemap (for [r s] [r #{:b}])))]
    (for [[r s] m :when (not (:b s))] r)))   

(def $ (ranges *eof*))


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

(def *free-follow* {:follow1 #{[#{[*min* *max*]}]}})

(defn follow [rule] (-> rule (nth 2) first (or *free-follow*)))

(defn close [init-states state]
  (fix-point (fn [state]
    (let [follows (set (map follow state))]
      (into (set state) (mapcat init-states follows)))) state))

(defn- assoc-multi [map k val]
  (assoc map k (conj (map k #{}) val)))

(defn- follow1-map [state]
  (let [shift-prods (filter (comp set? follow) state)]
    (-> (for [[k n [terminal & etc]] shift-prods 
              :let [p #{[k n etc]}], r terminal]
          [r p]) 
      rmap compact-rangemap)))

(defn- follow1-set [close prods]
  (let [dummy-state (map (partial conj [nil nil]) prods)]
    (-> dummy-state close follow1-map keys)))

(defn transitions [close tags state]
  (let [close-transitions #(into % (for [[k state] %] [k (close state)]))
        shifts (-> state follow1-map close-transitions)
        goto-prods (filter (comp keyword? follow) state)
        gotos (close-transitions
                (reduce (fn [gotos [k n [non-terminal & etc]]]
                          (assoc-multi gotos non-terminal [k n etc])) 
                     {} goto-prods))
        reduce-prods (filter (comp map? follow) state)
        reduces (-> (for [[k n :as prod] reduce-prods
                          :let [{follow-prods :follow1
                                 complement? :complement} (follow prod)
                                char-ranges (follow1-set close follow-prods)
                                char-ranges (if complement?
                                              (complement-ranges char-ranges) 
                                              char-ranges)]
                          char-range char-ranges] 
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
    [(loop [table {} todo #{state0}]
       (if-let [[state] (seq todo)]
         (let [transition (transitions state)
               table (assoc table state transition)
               new-states (remove table (to-states transition))
               todo (-> todo (disj state) (into new-states))]
           (recur table todo))
         table))
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

(defn- merge-nodes [nodes]
  (let [[seed nodes] (if (vector? (first nodes)) 
                       [(first nodes) (rest nodes)]
                       [[] nodes])]
    (reduce (fn self [nodes node]
              (cond
                (vector? node)
                  (let [top (peek nodes)]
                    (if (and (string? top) (string? (first node)))
                      (-> nodes pop (conj (str top (first node)))
                        (into (rest node)))
                      (into nodes node)))
                (char? node)
                  (let [top (peek nodes)]
                    (if (string? top)
                      (-> nodes pop (conj (str top node)))
                      (conj nodes (str node))))
                :else (conj nodes node))) seed nodes)))

(defn make-node [tag nodes]
  (let [content (merge-nodes nodes)] 
    (if tag
      {:tag tag :content content}
      content)))

(defn- shift [[stack unreducible-data data src :as stack+data] c new-state]
  (if (= *eof* c) 
    stack+data
    [(conj stack new-state) unreducible-data (conj data c) src]))

(defn- reduce-prod [[stack unreducible-data data src] action table]
  (let [[sym tag n] action
        stack (popN stack n)
        gotos (-> table (get (peek stack)) (nth 2))
        new-state (get gotos sym)
        stack (conj stack new-state)]
    (if (>= (count data) n)
      [stack unreducible-data 
        (conj (popN data n) (make-node tag (peekN data n))) src] 
      [stack (conj unreducible-data [data action]) [] src])))

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

(defn reset [stacks] (map (fn [[stack]] [stack [] [] stack]) stacks))

(defn stitchable? [a b]
  (every? (comp (set (map #(nth % 3) b)) first) a)) 

(defn- stitch-shift [[stack unreducible-data data src] more-data]
  [stack unreducible-data (into data more-data)]) 

(defn- stitch-reduce-prod [[stack unreducible-data data src] action]
  (let [[sym tag n] action]
    (if (>= (count data) n)
      [stack unreducible-data 
        (conj (popN data n) (make-node tag (peekN data n))) src]
      [stack (conj unreducible-data [data action]) [] src])))

(defn stitch [a b]
  (set
    (for [[stack-a unred-a data-a src-a :as sa] a
          [stack-b unred-b data-b src-b :as sb] b
          :when (= stack-a src-b)]
      (let [stack+data (reduce (fn [s [data action]]
                                 (-> s
                                   (stitch-shift data)
                                   (stitch-reduce-prod action)))
                         [stack-b unred-a data-a src-a] unred-b)
            stack+data (stitch-shift stack+data data-b)]
         stack+data))))

(comment
(require '[net.cgrand.enlive-html :as e]) 
(defn prd [stacks]
  (doseq [[_ _ data] stacks]
    (prn (->> data (make-node nil) e/emit* (apply str)))))

(def g {:S #{[:E $]}, 
        :E #{[:E (ranges \* \+) :B] 
             [:B]},
        :B #{[(ranges [\0 \9])]}})
(def table (lr-table g :S #{:S :B}))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "1+2") (step ttable "+3+4") (step1 ttable -1) prd) 
"<B>1</B>+<B>2</B>+<B>3</B>+<B>4</B>"

;; ambiguous 
(def g {:S #{[:E $]}, 
        :E #{[:E (ranges \* \+) :E] 
             [:B]},
        :B #{[(ranges [\0 \9])]}})
(def table (lr-table g :S #{:S :E}))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "1+2") (step ttable "+3+4") (step1 ttable -1) prd)

"<E><E><E>1</E>+<E>2</E></E>+<E><E>3</E>+<E>4</E></E></E>
<E><E><E>1</E>+<E><E>2</E>+<E>3</E></E></E>+<E>4</E></E>
<E><E>1</E>+<E><E>2</E>+<E><E>3</E>+<E>4</E></E></E></E>
<E><E>1</E>+<E><E><E>2</E>+<E>3</E></E>+<E>4</E></E></E>
<E><E><E><E>1</E>+<E>2</E></E>+<E>3</E></E>+<E>4</E></E>"
 
;; without follow restrictions 
(def g {:S #{[:A :AB $]},
        :A #{[(ranges \a) :A] 
             [(ranges \a)]},
        :AB #{[:AB (ranges \a \b)]
              [(ranges \a \b)]}})
(def table (lr-table g :S identity))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "aab") (step1 ttable -1) prd)
"<A>a</A><AB><AB>a</AB>b</AB>"
"<A>a<A>a</A></A><AB>b</AB>"

;; with follow(1) restrictions 
(def g {:S #{[:A :AB $]},
        :A #{[(ranges \a) :A] 
             [(ranges \a) {:follow1 #{[(ranges \b)]}}]},
        :AB #{[:AB (ranges \a \b)]
              [(ranges \a \b)]}})
(def table (lr-table g :S identity))
(def ttable (first table))
(def sop [[[(second table)] [] []]])
(-> sop (step ttable "aab") (step1 ttable -1) prd) 
"<A>a<A>a</A></A><AB>b</AB>"
 
;; incremental
(def g {:S #{[:E+ $]},
        :E+ #{[:E+ :E] [:E]}
        :E #{[(ranges [\a \z])] 
             [(ranges \():E+ (ranges \))]}})
(def table (lr-table g :S #{:E}))
(def ttable (first table))
(def sop [[[(second table)] [] [] nil]])
(-> sop (step ttable "a((aa)a)") (step1 ttable -1) prd)
"<E>a</E><E>(<E>(<E>a</E><E>a</E>)</E><E>a</E>)</E>"

(def c1 (-> sop (step ttable "a((aa)")))
(def c2 (-> (reset c1) (step ttable "a)")))
(stitchable? c1 c2)
true
(-> (stitch c1 c2) (step1 ttable -1) prd)
"<E>a</E><E>(<E>(<E>a</E><E>a</E>)</E><E>a</E>)</E>"

(def c1bis (-> sop (step ttable "a((aaa)")))
(stitchable? c1bis c2)
true
(-> (stitch c1bis c2) (step1 ttable -1) prd)
"<E>a</E><E>(<E>(<E>a</E><E>a</E><E>a</E>)</E><E>a</E>)</E>"
)

