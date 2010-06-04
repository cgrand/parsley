(ns net.cgrand.parsley.glr
  "A SGLR-inspired parser.")

;; a grammar is a map of keywords to sets of vector of keywords and terminals
;; empty productions are NOT allowed
;; TODO : define what constitues a terminal
;; a terminal is:
;; * a (sorted) set of codepoints ranges (inclusive bounds)

(def *min* Integer/MIN_VALUE)
(def *max* Integer/MAX_VALUE)
(def *eof* -1)


;; rangemaps
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

;; table computations
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
                        [char-range #{[k n (tags k)]}])
                  rmap compact-rangemap)]
    [shifts reduces gotos]))

(defn- to-states [[shifts _ gotos]]
  (concat (vals shifts) (vals gotos)))
     
(defn lr-table* [grammar start tags]
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

(defn number-syms-and-states [[table s0]]
  (let [syms (set (mapcat (comp keys peek) (vals table)))
        sym-nums (zipmap syms (iterate inc 0))
        states (cons s0 (keys (dissoc table s0)))
        state-nums (zipmap states (iterate inc 0))]
    (vec 
      (for [[shifts reduces gotos] (map table states)]
        [(into shifts (for [[k v] shifts] 
                        [k (state-nums v)]))
         (into reduces (for [[k actions] reduces]
                         [k (for [[sym n tag] actions] 
                              [(sym-nums sym) n tag])]))
         (vec (map (comp state-nums gotos) syms))]))))
        
(defn- fast-row [[shifts reduces gotos]]
  (let [cs (map one (range 0 128))
        ss (map shifts cs)
        rs (map reduces cs)]
    [(int-array (map #(or (when (empty? %2) %1) -1) ss rs))
     (to-array (map #(when-not (or %1 (next %2)) (first %2)) ss rs))
     (int-array (map #(or % -1) gotos))]))

(defn split-table [table]
  (let [fast-rows (map fast-row table)]
    [(to-array (map first fast-rows))
     (to-array (map second fast-rows))
     (to-array (map peek fast-rows))
     (to-array (map first table))
     (to-array (map second table))]))

(defn lr-table [grammar start tags]
  (-> (lr-table* grammar start tags) number-syms-and-states split-table))

(def boot-state [[(list 0) [] nil]])

;; the step function 
;; I tried to optimize "step" for:
;; * regular runs eg [a-z]+
;; * deterministic parts
;; * minimize construction
;;
;; To optimize (right) regular parts I must keep the last reduced substring
;; around.
;; To optimize deterministic part: process 1 "thread" on a bunch of chars at 
;; once rather the other way around

(defn popN [stack n]
  (if (pos? n)
    (recur (pop stack) (dec n))
    stack))

(defn- remove-last-shift [[stack events id]]
  (let [s (peek events)]
    (if (= s 1)
      [stack (pop events) id]
      [stack (conj (pop events) (dec s)) id])))

(defmacro shift-with {:private true} [f & etc]
  (concat [f] '(shift-state (conj stack state) events shift-i) etc))

(defmacro slow-path {:private true} []
  '(step1* state stack (persistent!  events) shift-i i (one c)))

(defn step1 [init-stack events tables #^String s]
  (let [[#^objects shifts #^objects reduces #^objects gotos 
         #^objects shifts* #^objects reduces*] tables
        n (int (count s))]
    (letfn [(qstep1* [state stack events shift-i i]
              (loop [state (int state) stack stack events (transient events) 
                     shift-i (int shift-i) i (int i)]
                 (if (> n i)
                   (let [c (int (.charAt s i))]
                     (if (> 128 c)
                       (let [shift-state (-> shifts #^ints (aget state) 
                                           (aget c))]
                         (if (neg? shift-state)
                           (if-let [action (-> reduces #^objects (aget state) 
                                             (aget c))]
                             (let [[sym n] action
                                   stack (popN stack (dec n))
                                   goto-state (-> gotos 
                                                #^ints (aget (int (peek stack)))
                                                (aget (int sym)))
                                   events (let [len (- i shift-i)]
                                            (if (pos? len)
                                              (-> events (conj! len) (conj! action))
                                              (conj! events action)))]
                               (recur goto-state stack events i i))
                             (slow-path))
                           (shift-with recur (unchecked-inc i))))
                       (slow-path)))
                   [[(conj stack state) 
                     (persistent! (if (< shift-i i) (conj! events (- i shift-i)) events)) 
                     init-stack]])))
            (step1* [state stack events shift-i i c]
              (concat 
                (when-let [shift-state (-> shifts* (aget (int state)) (get c))] 
                  (shift-with qstep1* (inc i)))  
                (mapcat 
                  #(let [[sym n] %
                         stack (popN stack (dec n))
                         goto-state (-> gotos 
                                      #^ints (aget (int (peek stack)))
                                      (aget (int sym)))
                         events (if (< shift-i i )
                                  (conj events (- i shift-i) %)
                                  (conj events %))]
                     (step1* goto-state stack events i i c)) 
                  (-> reduces* #^objects (aget (int state)) (get c)))))]
      (if s
        (qstep1* (peek init-stack) (pop init-stack) events 0 0)
        (->>
          (step1* (peek init-stack) (pop init-stack) events 0 0 (one *eof*))
          (map remove-last-shift))))))
      
;; 
(defn- count-nodes [nodes]
  (reduce #(if (string? %2) (+ %1 (count %2)) (inc %1)) 0 nodes))

(defn- my-peek [v]
  (nth v (unchecked-dec (.count #^clojure.lang.Counted v))))

(defn fold-nodes 
  "takes a string s, a vector of events and a number of nodes to read,
   returns [events nil unread-nodes-count]
   or [events nodes unread-chars-count]"
  [s events n]
  (loop [events (transient events) n (int n) i (count s) j (count s) folded ()]
    (cond
      (zero? n)
        (let [folded (if (< i j) (conj folded (subs s i j)) folded)]
          [(persistent! events) folded i])
      (zero? (.count #^clojure.lang.Counted events))
        (let [folded (if (< i j) (conj folded (subs s i j)) folded)
              m (count-nodes folded)]
          [(vec folded) nil (+ n m)])
      :else
        (let [event (my-peek events)
              etc (pop! events)]
          (if (number? event)
            (let [event (int event)]
              (if (< event n)
                (recur etc (- n event) (- i event) j folded)
                (recur (conj! etc (- event n)) (int 0) (- i n) j folded)))
            (let [[_ N tag] event]
              (if tag
                (let [[rem nodes N-or-i] (fold-nodes (subs s 0 i) (persistent! etc) N)
                      folded (if (< i j) (conj folded (subs s i j)) folded)]
                  (if nodes
                    (recur (transient rem) (dec n) (int N-or-i) (int N-or-i) 
                      (conj folded {:tag tag :content nodes}))
                    [(-> rem (conj [nil N-or-i tag]) (into folded))
                     nil (+ n (count-nodes folded))]))
                (recur etc (int (+ (dec n) N)) i j folded))))))))

(defn read-events [events s]
  (let [[events nodes N-or-i] (fold-nodes s events 1)]
    (cond
      nodes (conj (read-events events (subs s 0 N-or-i))
              (if (= 1 (count-nodes nodes))
                (first nodes)
                {:tag nil :content nodes}))
      (= 1 N-or-i) events
      :else (conj events [nil N-or-i nil]))))

(defn step
 "Advance all the threads by parsing the chunk s. When s is nil, it means EOF."
 [threads tables s]
  (for [[stack] (or threads boot-state)
        [stack events id] (step1 stack [] tables s)]
    [stack (read-events events (or s "")) id]))

(defn stitchable? [a b]
  (every? (comp (set (map #(nth % 2) b)) first) a))

(defn- data-conj [a x]
  (if (and (string? x) (string? (peek a)))
    (conj (pop a) (str (peek a) x))
    (conj a x)))
  
(defn- data-split [data n]
  (loop [rem data take () n n]
    (if (zero? n) 
      [rem take]
      (when-let [x (peek rem)]
        (cond
          (vector? x)
            nil
          (and (map? x) (nil? (:tag x)))
            (recur (pop rem) (concat (:content x) take) (dec n))
          (string? x)
            (let [m (count x)]
              (if (<= m n)
                (recur (pop rem) (conj take x) (- n m))
                [(conj (pop rem) (subs x 0 (- m n)))
                 (conj take (subs x (- m n)))]))
          :else
            (recur (pop rem) (conj take x) (dec n)))))))

(defn- stitch-data [a b]
  (loop [a a b (seq b)]
    (if-let [[x & etc] b]
      (if (vector? x)
        (let [[sym n tag] x]
          (if-let [[a content] (data-split a n)]
            (recur (conj a {:tag tag :content content}) etc)
            (into a b)))
        (recur (data-conj a x) etc))
      a)))

(defn- index [key-fn coll]
  (persistent! 
    (reduce (fn [m b] 
              (let [k (key-fn b)]
                (assoc! m k (conj (m k #{}) b))))
      (transient {}) coll)))

(defn stitch [a-threads b-threads]
  (let [bs (index #(nth % 2) b-threads)]
    (for [[a-stack a-events a-key] (or a-threads boot-state) 
          [b-stack b-events] (bs a-stack)]
      [b-stack (stitch-data a-events b-events) a-key])))

(comment
(require '[net.cgrand.enlive-html :as e]) 
(defn prd [stacks]
  (doseq [[_ _ data] stacks]
    (prn (->> data (core/make-node nil) e/emit* (apply str)))))

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

