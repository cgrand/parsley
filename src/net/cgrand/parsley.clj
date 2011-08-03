;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley
  "An experimental undocumented parser lib/DSL."
  (:require [net.cgrand.parsley.lrplus :as core]
            [net.cgrand.parsley.fold :as f]
            [net.cgrand.parsley.tree :as t]
            [net.cgrand.parsley.util :as u]))

;; A grammar consists of a map of keywords to:
;; * vectors (sequence)
;; * sets (alternatives)
;; * keywords (non-terminal or operators: :*, :+, :?)
;; * antything else (strings, patterns, fns and characters) are literals

(defprotocol RuleFragment
  (unsugar [fragment] "Remove sugarized forms")
  (collect [fragment unspaced top-rulename] "Collect \"anonymous\" productions")
  (develop [fragment rewrite space] 
    "normalize as a seq of seqs of keywords and terminals" ))

(defrecord Unspaced [item]
  RuleFragment
    (unsugar [this]
      (Unspaced. (unsugar item)))
    (collect [this unspaced top-rulename]
      (collect item true top-rulename))
    (develop [this rewrite space]
      (rewrite item #{[]})))

(defn unspaced [& specs]
  (Unspaced. (vec specs)))

(defrecord Root [item]
  RuleFragment
    (unsugar [this]
      (Root. (unsugar item)))
    (collect [this unspaced top-rulename]
      (collect item unspaced top-rulename))
    (develop [this rewrite space]
      (for [s1 space x (rewrite item space) s2 (if (empty? x) #{[]} space)]
        (concat s1 x s2))))

(defrecord Repeat+ [item]
  RuleFragment
    (unsugar [this]
      (Repeat+. (unsugar item)))
    (collect [this unspaced top-rulename]
      (let [kw (keyword (gensym (str top-rulename "_repeat+_")))
            alt #{[kw item] item}]
        (cons [this kw (if unspaced (Unspaced. alt) alt)] 
          (collect item unspaced top-rulename)))))

;; 2. collect new rules
(extend-protocol RuleFragment
  Object
    (unsugar [this]
      this)
    (collect [this unspaced top-rulename]
      nil)
    (develop [this rewrite space]
      [[this]])
    
  ;; a ref to another rule: add support for + ? or * suffixes
  clojure.lang.Keyword
    (unsugar [kw]
      (if-let [[_ base suffix] (re-matches #"(.*?)([+*?])" (name kw))] 
        (unsugar [(keyword base) (keyword suffix)])
        kw))
    (collect [this unspaced top-rulename]
      nil)
    (develop [this rewrite space]
      [[this]])
    
  ;; a set denotes an alternative
  clojure.lang.IPersistentSet
    (unsugar [this]
      (set (map unsugar this)))
    (collect [items unspaced top-rulename]
      (mapcat #(collect % unspaced top-rulename) items))
    (develop [items rewrite space]
      (mapcat #(rewrite % space) items))
    
  ;; a vector denotes a sequence, supports postfix operators :+ :? and :*
  clojure.lang.IPersistentVector
    (unsugar [this]
      (reduce #(condp = %2 
                 :* (conj (pop %1) #{[] (Repeat+. (peek %1))}) 
                 :+ (conj (pop %1) (Repeat+. (peek %1)))
                 :? (conj (pop %1) #{[](peek %1)})
                 (conj %1 (unsugar %2))) [] this))
    (collect [items unspaced top-rulename]
      (mapcat #(collect % unspaced top-rulename) items))
    (develop [items rewrite space]
      (reduce #(for [x (rewrite %2 space) sp space xs %1] 
                 (concat x (and (seq x) (seq xs) sp) xs))
        [()] (rseq items))))

(defn collect-new-rules
 "Collect new rules for new non-terminals corresponding to repeatitions."
 [grammar]
  (let [collected-rules 
         (mapcat (fn [[k v]] (collect v false (name k))) grammar)
        rewrites (into {} (for [[op k] collected-rules] [op k]))
        new-rules (set (vals rewrites))  
        grammar (into grammar (for [[_ k v] collected-rules
                                    :when (new-rules k)] [k v]))]
    [rewrites grammar]))

;; 3. develop-alts: 
(defn normalize
 "Normalize grammar as a map of non-terminals to set of seqs of
  terminals and non-terminals"
 ([grammar] (normalize grammar nil {}))
 ([grammar space rewrites]
  (let [helper (fn helper [item space]
                 (if-let [rw (rewrites item)]
                   [[rw]]
                   (develop item helper space)))
        space (helper space #{[]})]
    (into {} (for [[k v] grammar] [k (set (helper v space))])))))

;; 4. remove-empty-prods
(defn split-empty-prods [grammar]
  [(into {}
     (for [[k prods] grammar]
       [k (set (remove empty? prods))]))
   (into {}
     (for [[k prods] grammar
           :when (some empty? prods)]
       [k [() [k]]]))])

(defn- inline-prods [prods replacement-map]
  (letfn [(inline1 [prod]
            (if-let [[x & xs] (seq prod)]
              (for [a (replacement-map x [[x]]) b (inline1 xs)]
                (concat a b))
              [()]))]
    (mapcat inline1 prods)))

(defn- inline-empty-prods* [grammar]
  (let [[grammar empty-prods] (split-empty-prods grammar)]
    (into {}
      (for [[k prods] grammar]
        [k (-> prods (inline-prods empty-prods) set (disj [k]))]))))  
             
(defn inline-empty-prods [grammar]
  (u/fix-point inline-empty-prods* grammar)) 

(defn- private? [kw]
  (.endsWith (name kw) "-"))

(defn- basename [kw]
  (if (private? kw)
    (let [s (name kw)
          n (subs s 0 (dec (count s)))]
      (if-let [ns (namespace kw)]
        (keyword ns n)
        (keyword n)))
    kw))

;;;;;;;;;;;
(defn grammar [options-map rules]
  (let [[options-map rules] (if-not (map? options-map)
                              [{} (cons options-map rules)]
                              [options-map rules])
        rules (partition 2 rules)
        public-rulenames (remove private? (map first rules))
        {:keys [main space] :or {main (first public-rulenames) space #{[]}}} 
          options-map
        public-rulenames (set public-rulenames)
        rules (concat rules 
                [[::S (Root. main)] [::space (unspaced space)]])
        grammar (into {} (for [[name specs] rules]
                           [(basename name) (unsugar specs)]))
        [rewrites grammar] (collect-new-rules grammar)
        space (::space grammar)
        grammar (dissoc grammar ::space)
        grammar (-> grammar 
                  (normalize space rewrites) 
                  inline-empty-prods)]
  [grammar public-rulenames])) 

(defrecord Node [tag content]) ; for memory

(defn stepper [table options-map]
  (let [ops (merge
              {:make-node #(Node. %1 %2) 
               :make-leaf nil ; nil for identity
               :make-unexpected #(Node. ::unexpected [%1])
               :root-tag ::root}
              (select-keys options-map [:make-node :make-leaf :make-unexpected]))
        options-map (merge options-map ops)
        make-node (:make-node options-map)]
    ^{::options options-map} ; feeling dirty, metadata mamke me uneasy
    (fn self
      ([s]
        (let [a (self core/zero s) b (self a nil)]
          (when-let [r (f/stitch a b)]
            (make-node (:root-tag options-map) (:nodes (nth r 2))))))
      ([state s]
        (core/step table ops state s)))))

(defn parser [options-map & rules]
  (-> (grammar options-map rules) core/lr-table 
    core/number-states (stepper options-map)))

(defn- memoize-parser [f]
  (let [cache (atom nil)]
    (fn [input]
      (u/cond
        [last-result @cache
         new-result (f/rebase last-result input)]
          (if (identical? last-result new-result)
            last-result
            (reset! cache new-result))
        (reset! cache (f input))))))

(defn- memoize1 [parser s]
  (memoize-parser #(parser % s)))

(defn- memoize2 [mpa mpb]
  (memoize-parser #(let [a (mpa %)
                         b (mpb a)]
                     (f/stitch a b))))

(defn incremental-buffer [parser]
  {:buffer
     (t/buffer {:unit #(memoize1 parser %) 
                :plus memoize2 
                :chunk #(.split ^String % "(?<=\n)")
                :left #(subs %1 0 %2) 
                :right subs 
                :cat str})
   :eof-parser (memoize1 parser nil)
   :options (::options (meta parser))})

(defn edit [incremental-buffer offset length s]
  (update-in incremental-buffer [:buffer] t/edit offset length s))

(defn parse-tree [incremental-buffer]
  (let [f (t/value (:buffer incremental-buffer))
        a (f core/zero)
        b ((:eof-parser incremental-buffer) a)
        {:keys [make-node root-tag]} (-> incremental-buffer :options)]
    (when-let [x (f/stitch a b)]
      (make-node root-tag (:nodes (nth x 2)))))) 

