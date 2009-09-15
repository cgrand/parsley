(ns net.cgrand.parsley
  "An experimental undocumented parser lib/DSL.")

;; Parsley can parse ambiguous grammars and thus returns several results.
;; no support for left recursion (yet)

;; * a rule is made of _ops_
;; * parsing produces _events_
;; * the end result of a parse is (reduce reducer seed events)
;; * a parser's stitch function (eg default-stitch) must be associative
;;   and the parser's seed must be its zero (identity element)
;;   furthermore (stitch x (reduce reducer y events)) must be equal to
;;   (reduce (stitch x y) events) 

;;;; helpers
(defn- buffer [s op]
  #^{:type ::buffer} {:buffer s :op op})

;;;;;;;;;;;;;; ops interpreter
;;;; op interpreter fn
(defmulti #^{:private true} interpret-op (fn [_ op _ _] (type op)))

;; ref
(defmethod interpret-op clojure.lang.Keyword [rules kw s _]
  [[nil s [(rules kw)]]])

;; alternative
(defmethod interpret-op clojure.lang.IPersistentSet [_ ops s _]
  (map (fn [op] [nil s [op]]) ops)) 
  
;; sequence
(defmethod interpret-op clojure.lang.IPersistentVector [_ ops s _]
  [[nil s ops]])

;; buffer
(defmethod interpret-op ::buffer [_ {:keys [buffer op]} s _]
  [[nil (str buffer s) [op]]])
  
;; start-span & end-span
(defmethod interpret-op ::events [_ {:keys [events]} s _]
  [[events s nil]])

(defmethod interpret-op ::zero-or-more [_ {op :zero-or-more :as self} s _]
  [[nil s nil] [nil s [op self]]])

;; pass
(defmethod interpret-op nil [_ _ s _]
  [[nil s nil]])

;; fn
(defmethod interpret-op clojure.lang.Fn [_ f s eof]
  (let [result (f s eof)]
    (cond
      (string? result)
        [[[result] (subs s (count result)) nil]] 
      (= :need-more-input result)
        [[nil nil [(buffer s f)]]])))

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


;; reducer: partial-result * event -> partial-result
;; seed: partial-result
;; stitch: partial-result * partial-result -> partial-result
;; partial-result, seed and stitch must define a monoid
(defn parser* [rules seed reducer stitch]
 (with-meta [[nil seed [::main]]] 
    {::rules rules 
     ::seed seed 
     ::reducer #(if (= "" %2) %1 (reducer %1 %2)) 
     ::stitch stitch})) 

(defn step 
  ([states s] (step states s (not s)))
  ([states s eof]
    (let [{f ::reducer rules ::rules :as m} (meta states)]
      (with-meta (distinct (interpreter-step f rules states s eof)) m))))
      
(defn eof [states]
  (step states nil))
  
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

(defn stitchable? [a b]
  (let [b-keys (set (map first b))]
    (every? #(b-keys (% 2)) a))) 

(defn results [states]
  (for [[_ result ops] states :when (empty? ops)] result)) 

;; the grammar core language:
;; alt(ernative), cat(enate), zero-or-more, token, string, start-span, 
;; end-span or keyword
(defmulti compile-to-ops first)

(defmethod compile-to-ops ::alt [[_ & forms]]
  (set (map compile-to-ops forms)))

(defmethod compile-to-ops ::token [[_ & forms]]
  (vec (map compile-to-ops forms)))

(defmethod compile-to-ops ::cat [[_ & forms]]
  (vec (map compile-to-ops forms)))

(defmethod compile-to-ops ::zero-or-more [[_ form]]
  (let [op (compile-to-ops form)]
    #^{:type ::zero-or-more} {:zero-or-more op}))

(defmethod compile-to-ops ::string [[_ word]]
  (let [n (count word)]
    (fn self [#^String s eof]
      (cond 
        (< (count s) n)
          (when (and (not eof) (.startsWith word s))
              :need-more-input)
        (.startsWith s word)
          word))))

(defmethod compile-to-ops ::regex [[_ #^java.util.regex.Pattern pattern]]
  (fn [#^String s eof]
    (let [matcher (.matcher pattern s)
          found (.lookingAt matcher)]
      (cond
        (.hitEnd matcher)
          (cond
            (not eof) :need-more-input
            found (.group matcher))
        found 
          (.group matcher)))))

(defn- simple-class [class]
  (let [ns (namespace class)
        name (name class)]
    (keyword ns (subs name (-> name (.lastIndexOf ".") inc)))))
  
(defmethod compile-to-ops ::start-span [[_ class]]
  #^{:type ::events} {:events [[:start-span (simple-class class)]]})

(defmethod compile-to-ops ::end-span [[_ class]]
  #^{:type ::events} {:events [[:end-span (simple-class class)]]})

(defmethod compile-to-ops ::rule [[_ kw]]
  kw)

(defmethod compile-to-ops ::pass [_]
  nil)


#_(defn form-zip
 "Returns a zipper for nested list forms, given a root form"
 [root]
  (z/zipper #(and (seq? %) (seq %)) rest
    (fn [node children] (with-meta (cons (first node) children) (meta node)))
    root))

;; compile-spec turns a sugar-heavy grammar in a bunch of nested lists  
(defmulti #^{:private true} compile-spec #(if (seq? %) (first %) (type %)))

(defmethod compile-spec 'token [[_ & args]]
  (cons ::token (rest (compile-spec (vec args))))) 

;; a run
(defmethod compile-spec clojure.lang.IPersistentVector [v]
  (cons ::cat 
    (reduce (fn [v x]
              (condp = x
                '* (conj (pop v) (list ::zero-or-more (peek v)))
                '+ (conj v (list ::zero-or-more (peek v)))
                '? (conj (pop v) (list ::alt (peek v) '(::pass)))
                (conj v (compile-spec x)))) 
      [] v)))

;; an alternative
(defmethod compile-spec clojure.lang.IPersistentSet [s]
  (cons ::alt (map compile-spec s)))

;; a regex
(defmethod compile-spec java.util.regex.Pattern [pattern]
  (list ::regex pattern))

;; a terminal
(defmethod compile-spec String [word]
  (list ::string word))

;; a ref to another rule
(defmethod compile-spec clojure.lang.Keyword [kw]
  (let [n (name kw)]
    (if-let [x (#{\* \? \+} (last n))]
      (compile-spec
        [(keyword (subs n 0 (dec (count n)))) (symbol (str x))])
      (list ::rule kw))))

(defmethod compile-spec nil [_]
  (list ::pass))

;; else
#_(defmethod compile-spec :default [x]
  x)
  
;; interspace
(defmulti #^{:private true} interspace (fn [space form]
                                         (when (seq? form) (first form))))

(defmethod interspace ::cat [space [_ & forms]]
  `(::cat ~@(interpose space (map (partial interspace space) forms))))
  
(defmethod interspace ::token [space form]
  form)
  
(defmethod interspace ::rule [space form]
  form)
  
(defmethod interspace ::zero-or-more [space [_ form]]
  (let [form (interspace space form)]
    `(::alt
        (::pass)
        (::cat ~form (::zero-or-more (::cat ~space ~form))))))  

(defmethod interspace :default [space x]
  (if (seq? x)
    (cons (first x) (map (partial interspace space) (rest x)))
    x))  


  
(defn- compile-span [class space form]
  (let [form (compile-spec form)
        form (if space (interspace space form))
        form (if class
               `(::cat (::start-span ~class) ~form (::end-span ~class))
               form)]
    (compile-to-ops form)))

(defn- compile-rule [inlines space [name rhs]]
  `[~name ~(compile-span (when-not (inlines name) name) space rhs)])



      
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

(defmacro parser [options & rules ]
  (if (keyword? options)
    `(parser nil ~options ~@rules) 
    (let [; options
          default-opts {:seed `default-seed
                        :reducer `default-reducer 
                        :stitch `default-stitch
                        :main (first rules)}
          options (into default-opts options)
          {:keys [main seed reducer stitch space inline]} options
          inlines (into #{::intersticial-space ::alias-main ::main} (:inline options))
          
          base-rules [::intersticial-space 
                       (when space (list 'token space '?))
                      ::alias-main 
                       main
                      ::main
                       '(token ::intersticial-space ::alias-main ::intersticial-space)]
          space (when space '(::rule ::intersticial-space))
          rules (into {} 
                  (map (partial compile-rule inlines space) 
                    (partition 2 (concat base-rules rules))))]
      `(parser* ~rules ~seed ~reducer ~stitch))))