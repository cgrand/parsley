;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley
  "An experimental undocumented parser lib/DSL."
  (:require [net.cgrand.parsley.glr :as core]))

;; Parsley can parse ambiguous grammars and thus returns several results.
;; no support for left recursion (yet)

   
;; DSL support starts here

;; TODO: scratch that
;; once evaluated grammar consists of a map of keyword to:
;; * vectors (sequence)
;; * sets (alternatives)
;; * strings and characters (literals)
;; * maps (charsets)
;; * keywords (non-terminal)
;; * lists (special-ops: follow restrictions, rejects)

(defprotocol RuleFragment
  (collect [fragment token-mode top-rulename])
  (develop [fragment rewrite space]))

(defrecord Alt [items]
  RuleFragment
    (collect [this token-mode top-rulename]
      (mapcat #(collect % token-mode top-rulename) items))
    (develop [this rewrite space]
      (mapcat #(rewrite % space) items)))

(defrecord Seq [items]
  RuleFragment
    (collect [this token-mode top-rulename]
      (mapcat #(collect % token-mode top-rulename) items))
    (develop [this rewrite space]
      (reduce #(for [x (rewrite %2 space) xs %1] 
                 (concat x (and space (seq x) (seq xs) [space]) xs))
        [()] (rseq items))))

(defrecord Token [item]
  RuleFragment
    (collect [this token-mode top-rulename]
      (collect item true top-rulename))
    (develop [this rewrite space]
      (rewrite item nil)))

(defrecord Repeat+ [item]
  RuleFragment
    (collect [this token-mode top-rulename]
      (let [kw (keyword (gensym (str top-rulename "_repeat+_")))
            alt (Alt. [(Seq. [kw item]) item])]
        (cons [this kw (if token-mode (Token. alt) alt)] 
          (collect item token-mode top-rulename)))))

(defrecord Follow [item negative]
  RuleFragment
    (collect [this token-mode top-rulename]
      (collect item token-mode top-rulename))
    (develop [this rewrite space]
      [[{:follow1 (set (rewrite item space))
         :complement negative}]]))

;; 1. compile-spec turns a sugar-heavy grammar in a sugar-free grammar  
(defmulti #^{:private true} compile-spec type)

;; a vector denotes a sequence, supports postfix operators + ? and *
(defmethod compile-spec clojure.lang.IPersistentVector [specs]
  (Seq. 
    (reduce #(condp = %2 
             :* (conj (pop %1) (Alt. [(Seq. []) (Repeat+. (peek %1))])) 
             :+ (conj (pop %1) (Repeat+. (peek %1)))
             :? (conj (pop %1) (Alt. [(Seq. []) (peek %1)]))
             (conj %1 (compile-spec %2))) [] specs)))
  

;; a set denotes an alternative
(defmethod compile-spec clojure.lang.IPersistentSet [s]
  (Alt. (map compile-spec s)))

;; a ref to another rule: add support for + ? or * suffixes
(defmethod compile-spec clojure.lang.Keyword [kw]
  (if-let [[_ base suffix] (re-matches #"(.*?)([+*?])" (name kw))] 
    (compile-spec [(keyword base) (keyword suffix)])
    kw))

;; else pass through
(defmethod compile-spec :default [x]
  x)

(defn spec [& xs]
  (compile-spec (vec xs)))

;; DSL utils
(defn token [& specs]
  (Token. (apply spec specs)))

(defn ?= [& specs]
  (Follow. (apply spec specs) false))

(defn ?! [& specs]
  (Follow. (apply spec specs) true))

(defn any-of [s]
  (zipmap s s))

(defn none-of [& cs]
  (let [cps (map int (sort (apply str cs)))]
    (into {0 (dec (first cps)) (inc (last cps)) core/*max*}
      (map #(vector (inc %1) (dec %2)) cps (rest cps)))))

(def any-char {0 core/*max*})

(def $ {-1 -1})

;; 2. collect new rules
(extend-protocol RuleFragment
  nil
    (collect [this token-mode top-rulename]
      nil)
    (develop [this rewrite space]
      [()])
  String
    (collect [this token-mode top-rulename]
      nil)
    (develop [this rewrite space]
      [(map core/ranges this)])
  Character
    (collect [this token-mode top-rulename]
      nil)
    (develop [this rewrite space]
      [[(core/ranges this)]])
  clojure.lang.IPersistentMap 
    (collect [this token-mode top-rulename]
      nil)
    (develop [this rewrite space]
      [[(apply core/ranges this)]])
  Object
    (collect [this token-mode top-rulename]
      nil)
    (develop [this rewrite space]
      [[this]]))

(defn collect-new-rules [grammar]
  (let [collected-rules 
         (mapcat (fn [[k v]] (collect v false (name k))) grammar)
        rewrites (into {} (for [[op k] collected-rules] [op k]))
        new-rules (set (vals rewrites))  
        grammar (into grammar (for [[_ k v] collected-rules
                                    :when (new-rules k)] [k v]))]
    [rewrites grammar]))

;; 3. develop-alts: 
(defn normalize 
 ([grammar] (normalize grammar nil {}))
 ([grammar space rewrites]
  (letfn [(helper [item space]
            (if-let [rw (rewrites item)]
              [[rw]]
              (develop item helper space)))]
    (into {} (for [[k v] grammar] [k (set (helper v space))])))))

;; 4. remove-empty-prods
(defn- empty-prod? [prod]
  (every? :follow1 prod)) 

(defn split-empty-prods [grammar]
  [(into {}
     (for [[k prods] grammar]
       [k (set (remove empty-prod? prods))]))
   (into {}
     (for [[k prods] grammar
           :when (some empty-prod? prods)]
       [k [() [k]]]))])

(defn- inline-prods 
 ([prods replacement-map]
  (inline-prods prods replacement-map #{}))
 ([prods replacement-map collapsable?]
  (letfn [(inline1 [prod]
            (if-let [[x & xs] (seq prod)]
              (for [a (if (map? x)
                        [[(update-in x [:follow1] inline*)]]  
                        (replacement-map x [[x]])) 
                    b (inline1 xs)]
                (if (and (collapsable? (last a)) (collapsable? (first b)))
                  (concat a (rest b))
                  (concat a b)))
              [()]))
          (inline* [prods]
            (mapcat inline1 prods))]
    (inline* prods))))

(defn inline-empty-prods* [grammar space]
  (let [[grammar empty-prods] (split-empty-prods grammar)]
    (into {}
      (for [[k prods] grammar]
        [k (-> prods (inline-prods empty-prods #{space}) set (disj [k]))]))))  
             
(defn inline-empty-prods [grammar space]
  (core/fix-point #(inline-empty-prods* % space) grammar)) 



(defn- private? [kw]
  (let [s (name kw)]
    (when (.endsWith s "-")
      (keyword (subs s 0 (dec (count s)))))))

;;;;;;;;;;;
(defn grammar [options-map & rules]
  (let [[options-map rules] (if-not (map? options-map)
                              [{} (cons options-map rules)]
                              [options-map rules])
        rules (partition 2 rules)
        public-rulenames (remove private? (map first rules))
        {:keys [main space] :or {main (first public-rulenames)}} options-map
        public-rulenames (set public-rulenames)
        grammar (into {::main (spec (when space ::space) main $)
                       ::space (token space)}
                  (for [[name specs] rules]
                    [(or (private? name) name) (spec specs)]))
        [rewrites grammar] (collect-new-rules grammar)
        grammar (-> grammar (normalize (and space ::space) rewrites) 
                  (inline-empty-prods ::space))]
  [grammar ::main public-rulenames])) 

(defn stepper [table]
  (fn [state s]
    (core/step state table s)))

(defn parser [options-map & rules]
  (stepper (apply core/lr-table (apply grammar options-map rules))))

(comment
(def table (apply lr-table 
             (grammar {:main [:A*]
                       :space [" "*]}
               :letter- #{{\a \z, \A \Z, \0 \9} \-}
               :atom (token :letter+ (?! :letter))
               :A #{:atom [\( :A* \)]})))
(def ttable (first table))
(def sop [[[(second table)] [] [] nil]])
(-> sop (step ttable "cccccc") (step1 ttable -1) prd)
"'<A><atom>cccccc</atom></A>"
(-> sop (step ttable "aa aa") (step1 ttable -1) prd)
"<A><atom>aa</atom></A> <A><atom>aa</atom></A>"
(-> sop (step ttable "(mapcat (partial collect-rules tokenmode) (rest v))") (step1 ttable -1) prd)
"<A>(<A><atom>mapcat</atom></A> <A>(<A><atom>partial</atom></A> <A><atom>collectrules</atom></A> <A><atom>tokenmode</atom></A>)</A> <A>(<A><atom>rest</atom></A> <A><atom>v</atom></A>)</A>)</A>"
)