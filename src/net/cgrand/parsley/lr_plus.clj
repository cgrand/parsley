(ns net.cgrand.parsley.lr-plus
  "LR+ is LR(0) with contextual tokenizing.")

;; pushdown automaton
(defrecord TableState [token-matcher shifts reduce gotos])
(defn table-state [token-matcher shifts reduce goto] (TableState. token-matcher shifts reduce goto))

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
      (let [ns (remove nil? (map #(match % s eof) this))]
        (cond
          (some #{[-1]} ns)
            [-1]
          (next ns)
            (throw (Exception. (str "Ambiguous match for " (pr-str s) " by " (pr-str this))))
          :else 
            (first ns)))))

(defrecord CompoundTokenMatcher [ascii-dispatch tm]
  TokenMatcher
    (match [this s eof]
      (let [^String s s]
        (if (.isEmpty s)
          (match tm s eof)
          (let [cp (.codePointAt s 0)]
            (if (< cp (int 128))
              (when-let [tm (nth ascii-dispatch cp)]
                (match tm s eof))
              (match tm s eof)))))))

(defn match-prefix? [token-matcher ^String s]
  (when-let [[n] (match token-matcher s true)]
    (or (neg? n) (== n (.length s)))))

(defn matcher [tms]
  (when (seq tms)
    (if (next tms)
      (let [qtable (vec (map (fn [cp] 
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

(defn step1 [table state s eof]
  (let [[stack _ rem events] state
        s (if (= "" rem) s (str rem s))]
    (loop [stack (transient stack) events (transient events) s s wm (count stack)]
      (let [cs (table (my-peek stack))]
        (if-let [action (:reduce cs)]
          (let [[sym n] action
                stack (popN! stack n)
                cs (table (my-peek stack))
                wm (Math/min wm (count stack))]
            (recur (conj! stack ((:gotos cs) sym)) (conj! events action) s wm))
          (let [tm (:token-matcher cs)]
            (when-let [[n id] (match tm s eof)]
              (if (neg? n)
                [(persistent! stack) (dec wm) s (persistent! events)]
                (let [token (subs s 0 n)
                      s (subs s n)
                      wm (Math/min wm (count stack))]
                  (recur (conj! stack ((:shifts cs) id)) (conj! events token) s wm))))))))))

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
  (let [follows (mapvals (follow-map state) #(close %2))
        gotos (filter-keys follows keyword?)
        shifts (filter-keys (dissoc follows nil) (complement gotos))
        reduces (follows nil)
        reduction (when-let [[sym n] (first reduces)] [sym n (tags sym)])]
    (when (next reduces) 
      (throw (Exception. (str "reduce/reduce conflict " reduces))))
    (when (and reduction (seq shifts))
      (throw (Exception. (str "shift/reduce conflict " shifts " " reduces))))
    (table-state (matcher (keys shifts)) shifts reduction gotos)))

(defn to-states [{:keys [gotos shifts]}]
  (concat (vals gotos) (vals shifts)))

(defn lr-table* [[grammar start tags]]
  (let [init-states (mapvals grammar #(set (for [prod %2] [%1 (count prod) prod])))
        close (partial close init-states)
        state0 (-> start init-states close)
        transitions (partial transitions close tags)]
    [(loop [table {} todo #{state0}]
       (if-let [state (first todo)]
         (let [transition (transitions state)
               table (assoc table state transition)
               new-states (remove table (to-states transition))
               todo (-> todo (disj state) (into new-states))]
           (recur table todo))
         table))
     state0]))


(comment
  (comment
    E -> "(" E+ ")"
    E -> "x"
    E+ -> E+ E
    E+ -> E
    
    0 - "(" > 1
    0 - "x" > 5
    E -> ."(" E+ ")"
    E -> ."x"
    
    1 - E+ > 2
    1 - E > 6
    1 - "(" > 1
    1 - "x" > 5
    E -> "(" .E+ ")"
    E+ -> .E+ E
    E+ -> .E
    E -> ."(" E+ ")"
    E -> ."x"
    
    2 - ")" > 3
    2 - "(" > 1
    2 - "x" > 5
    2 - E > 4
    E -> "(" E+ .")"
    E+ -> E+ .E
    E -> ."(" E+ ")"
    E -> ."x"
    
    3
    E -> "(" E+ ")".
    
    4
    E+ -> E+ E.
    
    5
    E -> "x".
    
    6
    E+ -> E.
    )

    (def g 
      (let [w #"\w+"]
        {:E #{["(" :E+ ")"]
              [w]}
         :E+ #{[:E+ :E]
               [:E]}}))
  
    (let [[t s0] (lr-table* [g :E identity])]
      (step1 t [[s0] 0 "" []] "((hello)" false))
    
    (def t
      (let [w #"\w+"]
        (vec (map #(apply table-state %)
              [[(matcher #{"(" w}) {"(" 1 w 5} nil nil]
               [(matcher #{"(" w}) {"(" 1 w 5} nil {:E+ 2 :E 6}]
               [(matcher #{"(" w ")"}) {"(" 1 ")" 3 w 5} nil {:E 4}]
               [nil nil [:E 3 :E] nil]
               [nil nil [:E+ 2 :E+] nil]
               [nil nil [:E 1 :E] nil]
               [nil nil [:E+ 1 :E+] nil]]))))

    (let [s (apply str "(" (repeat 5e3 "(hello(world))"))] (time (count (step1 t [[0] 0 "" []] s false))))

    net.cgrand.parsley.lr-plus=> (step1 t [[0] 0 "" []] "((hello)" false)
    [[0 1 2] "" ["(" "(" "hello" [:E 1 :E] [:E+ 1 :E+] ")" [:E 3 :E] [:E+ 1 :E+]]]
)

