(ns net.cgrand.parsley.lr-plus)

(defrecord State [token-matcher shifts reduce gotos])
(defn state [token-matcher shifts reduce goto] (State. token-matcher shifts reduce goto))

(defprotocol TokenMatcher
  (match [this s eof]))

(extend-protocol TokenMatcher
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

(defn compound [tms]
  (let [qtable (vec (map (fn [cp] 
                 (let [s (str (char cp)) 
                       tms (filter #(match-prefix? % s) tms)]
                   (when (seq tms)
                     (if (next tms)
                       (set tms)
                       (first tms))))) (range 128)))]
    (CompoundTokenMatcher. qtable (set tms)))) 

(defn popN [stack n]
  (if (pos? n)
    (recur (pop stack) (dec n))
    stack))

(defn step1 [table state s eof]
  (let [[stack rem events] state
        s (if (= "" rem) s (str rem s))]
    (loop [stack stack events events s s]
      #_(prn stack events s)
      (let [cs (table (peek stack))]
        (if-let [action (:reduce cs)]
          (let [[sym n] action
                stack (popN stack n)
                cs (table (peek stack))]
            #_(prn action stack cs)
            (recur (conj stack ((:gotos cs) sym)) (conj events action) s))
          (let [tm (:token-matcher cs)]
            (when-let [[n id] (match tm s eof)]
              (if (neg? n)
                [stack s events]
                (let [token (subs s 0 n)
                      s (subs s n)]
                  (recur (conj stack ((:shifts cs) id)) (conj events token) s))))))))))

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
    
    (def t
      (let [w #"\w+"]
        (vec (map #(apply state %)
              [[(compound #{"(" w}) {"(" 1 w 5} nil nil]
               [(compound #{"(" w}) {"(" 1 w 5} nil {:E+ 2 :E 6}]
               [(compound #{"(" w ")"}) {"(" 1 ")" 3 w 5} nil {:E 4}]
               [nil nil [:E 3 :E] nil]
               [nil nil [:E+ 2 :E+] nil]
               [nil nil [:E 1 :E] nil]
               [nil nil [:E+ 1 :E+] nil]]))))

    (let [s (apply str "(" (repeat 5e3 "(hello(world))"))] (time (count (step1 t [[0] "" []] s false))))

    net.cgrand.parsley.lr-plus=> (step1 t [[0] "" []] "((hello)" false)
    [[0 1 2] "" ["(" "(" "hello" [:E 1 :E] [:E+ 1 :E+] ")" [:E 3 :E] [:E+ 1 :E+]]]
)

