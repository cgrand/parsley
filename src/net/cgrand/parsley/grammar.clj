;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.grammar
  (:require [net.cgrand.parsley.util :as u]))

(alias 'p 'net.cgrand.parsley) ; avoid circular dependency

;; A grammar production right-hand side consists of a combination of:
;; * vectors (sequence)
;; * sets (alternatives)
;; * keywords (non-terminal or operators: :*, :+, :?)
;; * antything else is considered as a literal (a "matcher")

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
      (if (= "" this) [] this))
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
(defn grammar 
  [options-map & rules]
  (let [[options-map rules] (if-not (map? options-map)
                              [{} (cons options-map rules)]
                              [options-map rules])
        rules (partition 2 rules)
        public-rulenames (remove private? (map first rules))
        {:keys [main space root-tag] 
         :or {main (first public-rulenames) root-tag ::p/root space #{[]}}} 
          options-map
        public-rulenames (-> (zipmap public-rulenames public-rulenames) 
                           (assoc ::p/S root-tag))
        rules (concat rules 
                [[::p/S (Root. main)] [::space (unspaced space)]])
        grammar (into {} (for [[name specs] rules]
                           [(basename name) (unsugar specs)]))
        [rewrites grammar] (collect-new-rules grammar)
        space (::space grammar)
        grammar (dissoc grammar ::space)
        grammar (-> grammar 
                  (normalize space rewrites)
                  (assoc ::canary #{[::p/S ::eof]})
                  inline-empty-prods)
        matches-empty (contains? (grammar ::canary) [::eof])
        grammar (dissoc grammar ::canary)]
  [grammar public-rulenames matches-empty])) 
