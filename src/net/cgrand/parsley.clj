(ns net.cgrand.parsley)

;; a parser is a function that takes a chunk of text (a String) and returns
;; a coll of [events n conts]

(defmulti interpret-cont (fn [_ cont _] (type cont)))

;; ref
(defmethod interpret-cont clojure.lang.Keyword [grammar kw s]
  [[nil s [(grammar kw)]]])

;; alternative
(defmethod interpret-cont clojure.lang.IPersistentSet [_ conts s]
  (map (fn [cont] [nil s [cont]]) conts)) 
  
;; sequence
(defmethod interpret-cont clojure.lang.IPersistentVector [_ conts s]
  [[nil s conts]])

;; terminal
(defmethod interpret-cont String [_ #^String terminal #^String s]
  (let [n (count terminal)]
    (cond 
      (< (count s) n)
        [[nil nil [{:buffer s :cont terminal}]]]
      (.startsWith s terminal)
        [[[terminal] (subs s (count terminal)) nil]])))

;; regex
(defmethod interpret-cont java.util.regex.Pattern 
 [_ #^java.util.regex.Pattern pattern #^String s]
  (let [matcher (.matcher pattern s)
        found (.lookingAt matcher)]
    (cond
      (.hitEnd matcher) 
        [[nil nil [{:buffer s :cont pattern}]]]
      found 
        [[[(.group matcher)] (subs s (.end matcher)) nil]])))
    
;; pass
(defmethod interpret-cont nil [_ _ s]
  [[nil s nil]])

(defmethod interpret-cont clojure.lang.IPersistentMap 
 [grammar {:keys [buffer cont]} s]
  [[nil (str buffer s) [cont]]])

;; fn
(defmethod interpret-cont clojure.lang.Fn [grammar cont s]
  (cont s))

(defn- interpreter-step1 [f grammar s [_ acc conts]]
  (let [k conts
        step1 (fn [s acc conts]
                (if-let [[cont & next-conts] (seq conts)]
                  (mapcat (fn [[ops s conts]]
                            (let [acc (reduce f acc ops)
                                  conts (concat conts next-conts)]
                                (if s
                                  (step1 s acc conts)  
                                  [[k acc conts]])))
                    (interpret-cont grammar cont s))
                  (when (empty? s)
                    [[k acc nil]])))]
    (step1 s acc conts)))

(defn- interpreter-step [f grammar states s]
  (mapcat (partial interpreter-step1 f grammar s) states))

(defn- start-span [class] 
  (let [ops [[:start-span class]]]
    (fn [s] [[ops s nil]])))  

(defn- end-span [class] 
  (let [ops [[:end-span class]]]
    (fn [s] [[ops s nil]])))  

(defn- zero-or-more [parser]
  (fn self [s] [[nil s nil] [nil s [parser self]]])) 

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;
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