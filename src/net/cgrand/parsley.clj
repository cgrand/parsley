(ns net.cgrand.parsley)

;;;;;;;;;;;;;; grammar interpreter
;;;; op interpreter fn
(defmulti interpret-cont (fn [_ cont _ _] (type cont)))

;; ref
(defmethod interpret-cont clojure.lang.Keyword [grammar kw s _]
  [[nil s [(grammar kw)]]])

;; alternative
(defmethod interpret-cont clojure.lang.IPersistentSet [_ conts s _]
  (map (fn [cont] [nil s [cont]]) conts)) 
  
;; sequence
(defmethod interpret-cont clojure.lang.IPersistentVector [_ conts s _]
  [[nil s conts]])

;; terminal
(defmethod interpret-cont String [_ #^String terminal #^String s eof]
  (let [n (count terminal)]
    (cond 
      (< (count s) n)
        (when-not eof
          [[nil nil [{:buffer s :cont terminal}]]])
      (.startsWith s terminal)
        [[[terminal] (subs s (count terminal)) nil]])))

;; regex
(defmethod interpret-cont java.util.regex.Pattern 
 [_ #^java.util.regex.Pattern pattern #^String s eof]
  (let [matcher (.matcher pattern s)
        found (.lookingAt matcher)]
    (cond
      (.hitEnd matcher)
        (if (and eof found)
          [[[(.group matcher)] (subs s (.end matcher)) nil]]
          [[nil nil [{:buffer s :cont pattern}]]])
      found 
        [[[(.group matcher)] (subs s (.end matcher)) nil]])))
    
;; pass
(defmethod interpret-cont nil [_ _ s _]
  [[nil s nil]])

;; buffer
(defmethod interpret-cont clojure.lang.IPersistentMap 
 [grammar {:keys [buffer cont]} s _]
  [[nil (str buffer s) [cont]]])

;; fn
(defmethod interpret-cont clojure.lang.Fn [grammar f s eof]
  (f s eof))

;;;; interpreter "loop" for 1 state
(defn- interpreter-step1 [f grammar s eof [_ acc conts]]
  (let [k conts
        step1 (fn step1 [s acc conts]
                (if-let [[cont & next-conts] (seq conts)]
                  (mapcat (fn [[ops s conts]]
                            (let [acc (reduce f acc ops)
                                  conts (concat conts next-conts)]
                                (if s
                                  (step1 s acc conts)  
                                  [[k acc conts]])))
                    (interpret-cont grammar cont s eof))
                  (when (empty? s)
                    [[k acc nil]])))]
    (step1 s acc conts)))

;; interpreter "loop" for "simultaneous" states
(defn- interpreter-step [f grammar states s eof]
  (mapcat (partial interpreter-step1 f grammar s) states))

;;;; helpers
(defn- start-span [class] 
  (let [ops [[:start-span class]]]
    (fn [s _] [[ops s nil]])))  

(defn- end-span [class] 
  (let [ops [[:end-span class]]]
    (fn [s _] [[ops s nil]])))  

(defn- zero-or-more [parser]
  (fn self [s _] [[nil s nil] [nil s [parser self]]])) 

;;;;;;;;;;;;;;;;;;;;;;
(defn- group-reduce 
 [k f seed coll]
  (persistent! (reduce #(let [key (k %2)]
                          (assoc! %1 key (f (%1 key seed) %2)))
                 (transient {}) coll)))

(defn stitch [op states-a states-b]
  (let [states-b-by-k (group-reduce first conj #{} states-b)]
    (mapcat (fn [[k a conts]]
              (for [[_ b conts] (states-b-by-k k)] [k (op a b)])) states-a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;; UNFINISHED / GARBAGE
(defn- step-stack [stack op]
  (if (vector? op)
    (condp = (first op)
      :start-span (cons [] stack)
      :end-span (let [[contents top & stack] stack
                      span (span (second op) contents)]
                  (when top
                    (cons (conj top span) stack))))
    (let [[top & stack] stack]
      (cons (conj top op) stack))))

(defn len [events] 
  (reduce + 0 (map #(:length % 0) events)))

(defn span [class contents]
  (if (string? contents)
    {:class class :contents nil :text contents :length (count contents)}
    {:class class :contents contents :length (len contents)}))   

      
(comment
(defgrammar
 [list ["(" expr * ")"]
  vector ["[" expr * "]"]
  map ["{" [expr expr]* "}"]
  set ["#{" expr * "}"]
  fun ["#(" expr * ")"]
  expr #{list vector map set fun}]
 ; :whitespace XXX
 :main expr))

(defmulti compile-spec type x)

;; a run
(defmethod compile-spec clojure.lang.IPersistentVector [v]
  (reduce (fn [v x]
    (cond
      (= '* x) (conj (pop v) (zero-or-more (peek v)))
      (= '+ x) (conj v (zero-or-more (peek v)))
      (= '? x) (conj (pop v) #{(peek v) nil})
      :else (conj v x))) [] (map compile-spec v)))

;; an alternative
(defmethod compile-spec clojure.lang.IPersistentSet [s]
  `#{~@(map compile-spec s}))

;; else
(defmethod compile-spec :default [x]
  x)

(defn grammar* [grammar main-rule]
  (let [main ((Y grammar) main-rule)]
    [['([]) [main]]])) 

(defn- compile-rule [grammar-sym [name rhs]]
  `[~(keyword name) (span-parser ~(keyword name) ~(compile-spec grammar-sym rhs))]) 
      
(defn- compile-rec-rule [grammar-sym [sym _]] 
  `(~sym [s#] 
     ((~grammar-sym ~(keyword sym)) s#)))
  
(defmacro grammar [rules & options]
  (let [rules (reduce (fn [rules [k v]] (assoc rules k (compile-spec v))) 
                {} (partition 2 rules))
        {:keys [main]} (apply hash-map options)
        main (or main (if (= 1 (count rules)) (key (first rules)) :main))] 
    `(grammar* 
       (fn [~grammar-sym]
         (letfn [~@(map (partial compile-rec-rule grammar-sym) rules)]
           ~(into {} (map (partial compile-rule grammar-sym) rules)))) 
       ~(keyword main))))

(def g (grammar [expr #{"-" ["(" expr * ")"]}] :main expr))

(def a (grammar
         {sum #{:prod [:prod "+" :sum]}
          prod #{:num [:num "*" :prod]}
          num #{"1" "0" ["(" :sum ")"]}}
         :main sum))