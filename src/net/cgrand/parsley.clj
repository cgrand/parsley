(ns net.cgrand.parsley)

;; Parsley can parse ambiguous grammars and thus returns several results.
;; no support for left recursion (yet)

;; * a rule is made of _ops_
;; * parsing produces _events_
;; * the end result of a parse is (reduce reducer seed events)
;; * a parser's stitch function (eg default-stitch) must be associative
;;   and the parser's seed must be its zero (identity element)
;;   furthermore (stitch x (reduce reducer y events)) must be equal to
;;   (reduce (stitch x y) events) 
 
;;;;;;;;;;;;;; ops interpreter
;;;; op interpreter fn
(defmulti interpret-op (fn [_ op _ _] (type op)))

;; ref
(defmethod interpret-op clojure.lang.Keyword [rules kw s _]
  [[nil s [(rules kw)]]])

;; alternative
(defmethod interpret-op clojure.lang.IPersistentSet [_ ops s _]
  (map (fn [op] [nil s [op]]) ops)) 
  
;; sequence
(defmethod interpret-op clojure.lang.IPersistentVector [_ ops s _]
  [[nil s ops]])

;; terminal
(defmethod interpret-op String [_ #^String terminal #^String s eof]
  (let [n (count terminal)]
    (cond 
      (< (count s) n)
        (when-not eof
          [[nil nil [{:buffer s :op terminal}]]])
      (.startsWith s terminal)
        [[[terminal] (subs s (count terminal)) nil]])))

;; regex
(defmethod interpret-op java.util.regex.Pattern 
 [_ #^java.util.regex.Pattern pattern #^String s eof]
  (let [matcher (.matcher pattern s)
        found (.lookingAt matcher)]
    (cond
      (.hitEnd matcher)
        (if (and eof found)
          [[[(.group matcher)] (subs s (.end matcher)) nil]]
          [[nil nil [{:buffer s :op pattern}]]])
      found 
        [[[(.group matcher)] (subs s (.end matcher)) nil]])))
    
;; pass
(defmethod interpret-op nil [_ _ s _]
  [[nil s nil]])

;; buffer
(defmethod interpret-op clojure.lang.IPersistentMap [_ {:keys [buffer op]} s _]
  [[nil (str buffer s) [op]]])

;; fn
(defmethod interpret-op clojure.lang.Fn [_ f s eof]
  (f s eof))

;;;; interpreter "loop" for 1 state
(defn- interpreter-step1 [f rules s eof [_ acc ops]]
  (let [k ops
        step1 (fn step1 [s acc ops]
                (if-let [[op & next-ops] (seq ops)]
                  (mapcat (fn [[events s ops]]
                            (let [acc (reduce f acc events)
                                  ops (concat ops next-ops)]
                                (if s
                                  (step1 s acc ops)  
                                  [[k acc ops]])))
                    (interpret-op rules op s eof))
                  (when (empty? s)
                    [[k acc nil]])))]
    (step1 s acc ops)))

;; interpreter "loop" for "simultaneous" states
(defn- interpreter-step [f rules states s eof]
  (mapcat (partial interpreter-step1 f rules (or s "") eof) states))

;;;; helpers
(defn- start-span [class] 
  (let [events [[:start-span class]]]
    (fn [s _] [[events s nil]])))  

(defn- end-span [class] 
  (let [events [[:end-span class]]]
    (fn [s _] [[events s nil]])))  

(defn- zero-or-more [parser]
  (fn self [s _] [[nil s nil] [nil s [parser self]]])) 




(comment
(defgrammar
 [list ["(" expr * ")"]
  vector ["[" expr * "]"]
  map ["{" [expr expr]* "}"]
  set ["#{" expr * "}"]
  fun ["#(" expr * ")"]
  expr #{list vector map set fun}]
 ; :whitespace XXX
 :main expr)
 
 ;;;;;;;;;;;;;;;;;;;;;;;;;

(def g (grammar [expr #{"-" ["(" expr * ")"]}] :main expr))

(def a (grammar
         {sum #{:prod [:prod "+" :sum]}
          prod #{:num [:num "*" :prod]}
          num #{"1" "0" ["(" :sum ")"]}}
         :main sum))
 )

(defn parser* [rules main seed reducer stitch]
 (with-meta [[nil seed [main]]] 
    {::rules rules 
     ::seed seed 
     ::reducer reducer 
     ::stitch stitch})) 

(defn step 
  ([states s] (step states s (not s)))
  ([states s eof]
    (let [{f ::reducer rules ::rules :as m} (meta states)]
      (with-meta (distinct (interpreter-step f rules states s eof)) m))))
  
(defn reset [states]
  (let [m (meta states)
        seed (::seed m)]
    (with-meta (map (fn [[k _ ops]] [k seed ops]) states) m)))

(defn- group-reduce 
 [k f seed coll]
  (persistent! (reduce #(let [key (k %2)]
                          (assoc! %1 key (f (%1 key seed) %2)))
                 (transient {}) coll)))

(defn- stitch* [stitch1 states-a states-b]
  (let [states-b-by-k (group-reduce first conj #{} states-b)]
    (mapcat (fn [[k a ops-a]]
              (for [[_ b ops] (states-b-by-k ops-a)] [k (stitch1 a b) ops])) 
      states-a)))
              
(defn stitch [a b]
  (let [m (meta a)
        stitch1 (::stitch m)]
    (with-meta (stitch* stitch1 a b) m))) 

(defn results [states]
  (for [[_ result ops] states :when (empty? ops)] result)) 



(defmulti #^{:private true} compile-spec type)

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
  (set (map compile-spec s)))

;; else
(defmethod compile-spec :default [x]
  x)

(defn- compile-rule [[name rhs]]
  `[~name [(start-span ~name) ~(compile-spec rhs) (end-span ~name)]]) 
      
(defn span [class contents]
  (if (string? contents)
    {:class class :contents nil :text contents :length (count contents)}
    {:class class :contents contents 
     :length (reduce #(+ %1 (or (:length %2) (count %2))) 0 contents)}))   

(def default-seed [[] []])

(defn- alter-top [stack f & args]
  (if (seq stack)
    (conj (pop stack) (apply f (peek stack) args))
    stack))

(defn- push-string [stack s]
  (if (string? (peek stack))
    (conj (pop stack) (str (peek stack) s))
    (conj stack s)))

(defn default-reducer [[events stack] event]
  (cond
    (= (first event) :start-span)
      [events (conj stack [])]
    (seq stack)
      (cond 
        (string? event)
          [events (alter-top stack push-string event)]
        (map? event)
          [events (alter-top stack conj event)]
        (= (first event) :end-span)
          (let [span (span (second event) (peek stack))
                etc (pop stack)]
            (if (seq etc)
              [events (alter-top etc conj span)]
              [(conj events span) etc])))
    :else
      [(conj events event) stack]))

(defn default-stitch [a [events-b stack-b]]
  (let [[events stack] (reduce default-reducer a events-b)]
    [events (into stack stack-b)]))

(defmacro parser [rules & options]
  (let [rules (into {} (map compile-rule rules))
        default-opts {:seed `default-seed
                      :reducer `default-reducer 
                      :stitch `default-stitch}
        options (into default-opts (apply hash-map options))
        {:keys [main seed reducer stitch]} options 
        main (or main (if (= 1 (count rules)) (key (first rules)) :main))] 
    `(parser* ~rules ~main ~seed ~reducer ~stitch)))

(comment
;;;;;;;;;; EXAMPLE USAGE
(def simple-lisp 
  (parser 
    {:main [[:w ? :expr]* :w ?]
     :expr #{:symbol ["("[:w ? :expr]* :w ? ")"]}
     :symbol #"\w+"
     :w #"\s+"}))   

;; helper functions to display results in a more readable way 
(defn terse-result [[items _]]
  (map (fn self [item]
         (if (map? item)
           (cons (:class item) (map self (:contents item)))
           item)) items))

(defn prn-terse [results]
  (doseq [result results]
    (prn (terse-result result))))
    
;; let's parse this snippet
(-> simple-lisp (step "()(hello)") results prn-terse)
;;> ((:main (:expr "()") (:expr "(" (:expr (:symbol "hello")) ")")))

;; let's parse this snippet in two steps
(-> simple-lisp (step "()(hel") (step "lo)") results prn-terse)
;;> ((:main (:expr "()") (:expr "(" (:expr (:symbol "hello")) ")")))

;; and now, the incremental parsing!
(let [c1 (-> simple-lisp reset (step "()(hel"))
      c2 (-> c1 reset (step "lo)" nil))
      _ (-> (stitch c1 c2) results prn-terse) ; business as usual
      c1b (-> simple-lisp reset (step "(bonjour)(hel")) ; an updated 1st chunk
      _ (-> (stitch c1b c2) results prn-terse) 
      c1t (-> simple-lisp reset (step "(bonjour hel")) ; an updated 1st chunk
      _ (-> (stitch c1t c2) results prn-terse)] 
  nil)
;;> ((:main (:expr "()") (:expr "(" (:expr (:symbol "hello")) ")")))
;;> ((:main (:expr "(" (:expr (:symbol "bonjour")) ")") (:expr "(" (:expr (:symbol "hello")) ")")))
)