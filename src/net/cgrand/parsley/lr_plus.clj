(ns net.cgrand.parsley.lr-plus
  "LR+ is LR(0) with contextual tokenizing."
  (:require [net.cgrand.parsley.fold :as f]
            [net.cgrand.parsley.util :as u]))

;; pushdown automaton
(defrecord TableState [token-matcher shifts reduce gotos accept?])
(defn table-state [token-matcher shifts reduce goto accept?] 
  (TableState. token-matcher shifts reduce goto accept?))

(defprotocol TokenMatcher
  (match [this s eof]))

(extend-protocol TokenMatcher
  Character
    (match [this ^String s eof]
      (cond
        (.isEmpty s)
          (when-not eof [-1])
        (= (.charAt s 0) this)
          [1 this] 
        :else
          nil))
  String
    (match [this ^String s eof]
      (cond
        (.startsWith s this)
          [(.length this) this] 
        eof
          nil
        (.startsWith this s)
          [-1]))
  java.util.regex.Pattern
    (match [this s eof]
      (let [m (re-matcher this s)
            found (.lookingAt m)]
        (cond
          (and (not eof) (.hitEnd m))
            [-1]
          found 
            [(.end m) this])))
  clojure.lang.IFn
    (match [this s eof]
      (this s eof))
  clojure.lang.APersistentSet
    (match [this s eof]
      (let [ns (filter identity (map #(match % s eof) this))]
        (cond
          (some #{[-1]} ns)
            [-1]
          (next ns)
            (throw (Exception. (str "Ambiguous match for " (pr-str s) " by " (pr-str this))))
          :else 
            (first ns)))))

(declare eq-ctm)

(deftype CompoundTokenMatcher [^objects ascii-dispatch tm]
  TokenMatcher
    (match [this s eof]
      (u/cond
        :let [^String s s]
        (.isEmpty s)
          (match tm s eof)
        :let [cp (.codePointAt s 0)]
        (< cp (int 128))
          (when-let [tm (aget ascii-dispatch cp)]
            (match tm s eof))
        (match tm s eof)))
  Object
    (hashCode [_] (.hashCode tm))
    (equals [this that]
      (boolean (eq-ctm this that)))
    (toString [_] (str tm)))

(defn- eq-ctm [^CompoundTokenMatcher this that]
  (and (instance? CompoundTokenMatcher that) 
       (= (.tm this) (.tm ^CompoundTokenMatcher that))))

(defn match-prefix? [token-matcher ^String s]
  (when-let [[n] (match token-matcher s false)]
    (or (neg? n) (== n (.length s)))))

(defn matcher [tms]
  (when (seq tms)
    (if (next tms)
      (let [qtable (to-array
                     (map (fn [cp] 
                            (let [s (str (char cp)) 
                                  tms (filter #(match-prefix? % s) tms)]
                              (when (seq tms)
                                (if (next tms)
                                  (set tms)
                                  (first tms))))) (range 128)))]
        (CompoundTokenMatcher. qtable (set tms)))
      (first tms))))

(defn my-peek [v]
  (nth v (unchecked-dec (.count #^clojure.lang.Counted v))))

(defn popN! [stack n]
  (if (pos? n)
    (recur (pop! stack) (dec n))
    stack))

(defn step1
  "Returns [stack water-mark buffer events] where stack is the new stack,
   water-mark the number of items at the bottom of the stack which didn't took 
   part in this step, buffer the remaining string to be tokenized, events the
   parsing events."
 [table state s eof]
  (let [[stack _ rem events] state
        s (if (= "" rem) s (str rem s))]
    (loop [stack (transient (or stack [0])) events events s s wm (count stack)]
      (u/cond
        :when-let [cs (table (my-peek stack))]
        (and (empty? s) (:accept? cs))
          [(persistent! stack) (dec wm) "" events]
        [action (:reduce cs)]
          (let [[sym n] action
                stack (popN! stack n)
                cs (table (my-peek stack))
                wm (Math/min wm (count stack))]
            (recur (conj! stack ((:gotos cs) sym)) (conj events action) s wm))
        :when-let [tm (:token-matcher cs)]
        [[n id] (match tm s eof)]
          (if (neg? n)
            [(persistent! stack) (dec wm) s events]
            (let [token (subs s 0 n)
                  s (subs s n)
                  wm (Math/min wm (count stack))]
              (recur (conj! stack ((:shifts cs) id)) (conj events token) s wm)))
        (when-not (empty? s) 
          (recur stack (conj events (f/make-unexpected (subs s 0 1)))
                 (subs s 1) wm))))))

(def zero [[[0] ""] 0 f/empty-folding-queue nil])

(defn step [table state s]
  (u/when-let [[[stack rem :as start]] state
               [new-stack water-mark new-rem events] 
               (step1 table [stack nil rem f/empty-folding-queue] (or s "") (nil? s))]
    [[new-stack new-rem] water-mark events start]))

;; LR+ table construction
(defn fix-point [f init]
  (let [v (f init)]
    (if (= v init)
      init
      (recur f v))))

(defn close [init-states state]
  (fix-point (fn [state]
               (let [follows (map #(first (nth % 2)) state)]
                 (into state (mapcat init-states follows)))) 
    (set state)))

(defn mapvals [map f]
  (into map (for [[k v] map] [k (f k v)])))

(defn filter-keys [map pred]
  (into {} (for [kv map :when (pred (key kv))] kv)))

(defn follow-map [state]
  (apply merge-with into 
    (for [[k n prod] state] {(first prod) #{[k n (next prod)]}})))

(defn transitions [close tags state]
  (u/cond
    :let [follows (mapvals (follow-map state) #(close %2))
          gotos (filter-keys follows keyword?)
          shifts (filter-keys (dissoc follows nil) (complement gotos))
          reduces (follows nil)
          accepts (filter (fn [[s _ r]] (= 0 s)) reduces)
          reduces (reduce disj reduces accepts)
          reduction (when-let [[sym n] (first reduces)] [sym n (tags sym)])
          accept? (and (seq accepts) true)]
    (next reduces) 
      (throw (Exception. (apply str "at state " state "\n  reduce/reduce conflict " (interpose "\n" reduces))))
    (and reduction (seq shifts))
      (throw (Exception. (str "at state " state "\n shift/reduce conflict " shifts "\n" reduces)))
    (table-state (matcher (keys shifts)) shifts reduction gotos accept?)))

(defn to-states [{:keys [gotos shifts]}]
  (concat (vals gotos) (vals shifts)))

(defn lr-table [[grammar tags]]
  (let [grammar (-> grammar (dissoc :net.cgrand.parsley/S) 
                  (assoc 0 (:net.cgrand.parsley/S grammar)))
        init-states (mapvals grammar #(set (for [prod %2] [%1 (count prod) prod])))
        close (partial close init-states)
        state0 (-> 0 init-states close)
        transitions (partial transitions close tags)
        table (loop [table {} todo #{state0}]
                (if-let [state (first todo)]
                  (let [transition (transitions state)
                        table (assoc table state transition)
                        new-states (remove table (to-states transition))
                        todo (-> todo (disj state) (into new-states))]
                    (recur table todo))
                  table))
        ;; TODO think harder about 0 and state0 being the same thing
        table (assoc table 0 (assoc (table state0) :accept? true))]
    table))

(defn number-states [table]
  (let [table-without-start (dissoc table 0)
        mapping (zipmap (cons 0 (keys table-without-start)) (range))
        renum (fn [m] (reduce #(update-in %1 [%2] mapping) m (keys m)))
        syms (set (keep #(-> % :reduce first) (vals table)))
        syms-mapping (zipmap syms (range))
        empty-goto (vec (repeat (count syms) nil))
        renum-gotosyms (fn [goto] (reduce (fn [goto [sym state]]
                                            (assoc goto (syms-mapping sym) state))
                                       empty-goto goto))]
    (vec
      (for [{shifts :shifts gotos :gotos :as v} 
            (cons (get table 0) (vals table-without-start))]
        (assoc v :reduce (when-let [[sym n tag] (:reduce v)] [(syms-mapping sym) n tag])
               :shifts (renum shifts) :gotos (-> gotos renum renum-gotosyms))))))

(comment
    (def g 
      {:E #{["(" :E+ ")"]
            [#"\w+"]}
       :E+ #{[:E+ :E]
             [:E]}})
  
    (let [t (lr-table [g :E identity])]
      (step t zero "((hello)"))
    
)

