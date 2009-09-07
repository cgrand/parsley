(ns net.cgrand.parsley)

(defn len [spans] 
  (reduce + 0 (map :length spans)))
  
(defn span [class contents]
  (if (string? contents)
    {:class class :contents nil :text contents :length (count contents)}
    {:class class :contents contents :length (len contents)}))
    
(defn alt 
 [& parsers]
  (fn [s] 
    (mapcat #(% s) parsers)))

(defn cat
 [& parsers]
  (fn [s]
    (when-let [[parser & parsers] (seq parsers)]
      (for [[spans n conts] (parser s)]
        [spans n (concat conts parsers)]))))
  
(defn string-parser [class text]
  (let [len (count text)
        ok [[[(span class text)] len nil]]
        parser 
          (fn parser [text]
            (fn [s]
                (let [n (count s)]
                  (if (<= len n)
                    (when (= text (subs s 0 len))
                      ok)
                    (when (= s (subs text 0 n))
                      (parser (subs text n)))))))]
    (parser text)))

(defn- start-span [class] [:start-span class])  

(defn span-parser [class parser]
  (let [end-ops [[:end-span class]]
        start-op (start-span class)
        startify (fn [parser]
                   (fn [s]
                     (for [[ops n conts] (parser s)]
                       [(cons start-op ops) n conts])))
        endify (fn endify [parser]
                 (fn [s]
                   (for [[ops n conts] (parser s)]
                     (if (seq conts)
                       [ops n (concat (butlast conts) [(endify (last conts))])] 
                       [(concat ops end-ops) n nil]))))]
    (-> parser startify endify)))

(def pass (constantly [[nil 0 nil]]))

(defn- Y [f]
  (let [g (memoize (fn [self] (f #((self self) %))))]
    (g g)))    

(defn repeat-parser [parser]
  (Y (fn [self]
       (alt (cat parser self) pass))))

;;;;;;;;;;;;;;;;;;;;;;

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
      
(defn- consume
 [conts s]
  (when-let [[cont & conts] (seq conts)]
    (mapcat (fn [[ops n new-conts]]
              (let [conts (concat new-conts conts)]
                (if (< n (count s))
                  (for [[o c] (consume conts (subs s n))]
                    [(concat ops o) c])
                  [[ops conts]])))
      (cont s))))

(defn step
 "Consumes s and returns a seq of states." 
 [states s]
  (if (seq s)
    (letfn [(step1 [[stack conts]]
              (for [[ops conts] (consume conts s)]
                [(reduce step-stack stack ops) conts]))]
      (mapcat step1 states))
    states)) 

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

(defmulti compile-rhs (fn [grammar-sym x] (type x)))

;; a run

(defmethod compile-rhs clojure.lang.IPersistentVector
 [grammar-sym v]
  (let [v (reduce (fn [v x]
                    (cond
                      (= '* x) (conj (pop v) `(repeat-parser ~(peek v)))
                      (= '+ x) (conj (pop v) `(cat ~(peek v) (repeat-parser ~(peek v))))
                      :else (conj v (compile-rhs grammar-sym x)))) [] v)]
    `(cat ~@v)))

;; an alternative
(defmethod compile-rhs clojure.lang.IPersistentSet
 [grammar-sym s]
  `(alt ~@(map (partial compile-rhs grammar-sym) s)))

;; a literal string
(defmethod compile-rhs String
 [grammar-sym s]
  `(string-parser nil ~s))

;; else
(defmethod compile-rhs :default
 [grammar-sym x]
  x)

(defn grammar* [grammar main-rule]
  (let [main ((Y grammar) main-rule)]
    [['([]) [main]]])) 

(defn- compile-rule [grammar-sym [name rhs]]
  `[~(keyword name) (span-parser ~(keyword name) ~(compile-rhs grammar-sym rhs))]) 
      
(defn- compile-rec-rule [grammar-sym [sym _]] 
  `(~sym [s#] 
     ((~grammar-sym ~(keyword sym)) s#)))
  
(defmacro grammar [rules & options]
  (let [rules (partition 2 rules) 
        {:keys [main] :or {main 'main}} (apply hash-map options)
        grammar-sym (gensym "grammar")]
    `(grammar* 
       (fn [~grammar-sym]
         (letfn [~@(map (partial compile-rec-rule grammar-sym) rules)]
           ~(into {} (map (partial compile-rule grammar-sym) rules)))) 
       ~(keyword main))))

(def g (grammar [expr #{"-" ["(" expr * ")"]}] :main expr))

(def a (grammar
         {:sum #{:prod [:prod "+" :sum]}
          :prod #{:num [:num "*" :prod]}
          :num #{"1" "0" ["(" :sum ")"]}}
         :main :sum))