;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.lrplus
  "LR+ is LR(0) with contextual tokenizing."
  (:require [net.cgrand.parsley.fold :as f]
            [net.cgrand.parsley.util :as u]
            [net.cgrand.parsley.stack :as st]))

(alias 'p 'net.cgrand.parsley) ; avoid circular dependency

; I independently figured out the sale technique as the one described
; in this paper: Context-Aware Scanning for Parsing Extensible Languages
; http://www.umsec.umn.edu/publications/Context-Aware-Scanning-Parsing-Extensible-Language

;; pushdown automaton
(defrecord TableState [token-matcher shifts reduce gotos accept eof])
(defn table-state [token-matcher shifts reduce goto accept & [eof]] 
  (TableState. token-matcher shifts reduce goto accept eof))

(defprotocol TokenMatcher
  (match [this s eof]))

(extend-protocol TokenMatcher
  nil
    (match [this ^String s eof]
      nil)
  Character
    (match [this ^String s eof]
      (cond
        (zero? (.length s))
          (when-not eof [-1])
        (== (int (.charAt s 0)) (int (.charValue this)))
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
      (let [ns (keep #(match % s eof) this)]
        (cond
          (some #{[-1]} ns)
            [-1]
          (next ns)
            (throw (Exception. (str "Ambiguous match for " (pr-str s) " by " (pr-str this))))
          :else 
            (first ns)))))

(deftype UnionMatcher [^objects matchers]
  TokenMatcher
  (match [this s eof]
    (loop [i (alength matchers) r nil]
      (u/cond
        (zero? i) r
        :let [i (unchecked-dec i)
              m (aget matchers i)
              mr (match m s eof)]
        (= [-1] mr) [-1]
        (and r mr) 
          (throw (Exception. (str "Ambiguous match for " (pr-str s) " by " (pr-str this))))
        (recur i (or r mr))))))

(declare eq-ctm)

(deftype CompoundTokenMatcher [^objects ascii-dispatch tm]
  TokenMatcher
    (match [this s eof]
      (u/cond
        :let [^String s s]
        (zero? (.length s))
          (match tm s eof)
        :let [cp (.codePointAt s 0)]
        (< cp (int 128))
          (when-let [tm (aget ascii-dispatch cp)]
            (match tm s eof))
        (match tm s eof)))
  Object
    (hashCode [_] (.hashCode tm))
    (equals [this that]
      (boolean (eq-ctm this that)))
    (toString [_] (str tm)))

(defn- eq-ctm [^CompoundTokenMatcher this that]
  (and (instance? CompoundTokenMatcher that) 
       (= (.tm this) (.tm ^CompoundTokenMatcher that))))

(defn prefix-matcher [token-matcher ^String s]
  (u/cond
    :when-let [[n :as r] (match token-matcher s false)]
    (neg? n) token-matcher
    (constantly r)))

(defn matcher [tms]
  (when (seq tms)
    (if (next tms)
      (let [qtable (to-array
                     (map (fn [cp] 
                            (let [s (str (char cp)) 
                                  tms (filter #(prefix-matcher % s) tms)]
                              (when (seq tms)
                                (if (next tms)
                                  (UnionMatcher. (to-array (set tms)))
                                  (first tms))))) (range 128)))]
        (CompoundTokenMatcher. qtable (set tms)))
      (first tms))))

(defn- count-unexpected [tm s eof]
  (loop [n 1]
    (let [suf (subs s n)] 
      (if (or (match tm suf eof) (empty? suf))
        n
        (recur (inc n))))))

(defn step1
  "Returns [stack water-mark buffer events] where stack is the new stack,
   water-mark the number of items at the bottom of the stack which didn't took 
   part in this step, buffer the remaining string to be tokenized, events the
   parsing events."
 [table ops stack rem s]
  (when (nil? stack)
    (throw (IllegalStateException. "Can't accept more input past EOF.")))
  (let [eof (nil? s)
        s (or s "")
        s (if (= "" rem) s (str rem s))
        fq (f/folding-queue ops)
        stack (st/stack stack)]
    (loop [^String s s]
      (u/cond
        :when-let [state (st/peek! stack)
                   cs (table state)]
        [[sym n tag] (and (zero? (.length s)) (:accept cs))] 
          (if eof
            (do
              (f/node! fq tag n)
              [(assoc @stack :stack nil) "" @fq])
            [@stack "" @fq])
        [[sym n tag] (:reduce cs)]
          (let [cs (-> stack (st/popN! n) st/peek! table)]
            (f/node! fq tag n)
            (st/push! stack ((:gotos cs) sym))
            (recur s))
        :let [tm (:token-matcher cs)]
        [[n id] (match tm s eof)]
          (if (neg? n)
            [@stack s @fq]
            (let [token (subs s 0 n)
                  s (subs s n)
                  state ((:shifts cs) id)]
              (f/leaf! fq token)
              (st/push! stack state)
              (recur s)))
        (not (empty? s)) ; unexpected input
          (let [n (count-unexpected tm s eof)]
            (f/unexpected! fq (subs s 0 n))
            (recur (subs s n)))
        ; unexpected eof
        (let [[sym n tag] (:eof cs)
              cs (-> stack (st/popN! n) st/peek! table)
              _ (f/node! fq tag n)]
          (st/push! stack ((:gotos cs) sym))
          (recur s))))))

(def zero [[[0] ""] 0 nil nil])

(defn step [table ops state s]
  (u/when-let [[[stack rem :as start]] state
               [{:keys [watermark stack]} rem events] 
                 (step1 table ops stack rem s)]
    [[stack rem] watermark events start]))

;; LR+ table construction
(defn close [init-states state]
  (u/fix-point (fn [state]
               (let [follows (map #(first (nth % 2)) state)]
                 (into state (mapcat init-states follows)))) 
    (set state)))

(defn filter-keys [map pred]
  (into {} (for [kv map :when (pred (key kv))] kv)))

(defn follow-map [state]
  (apply merge-with into {}
    (for [[k n prod] state] {(first prod) #{[k n (next prod)]}})))

(defn transitions [close tags state]
  (u/cond
    :let [follows (u/map-vals (follow-map state) #(close %2))
          gotos (filter-keys follows keyword?)
          shifts (filter-keys (dissoc follows nil) (complement gotos))
          reduces (follows nil)
          accepts (filter (fn [[s _ r]] (= 0 s)) reduces)
          reduces (reduce disj reduces accepts)
          reduction (when-let [[sym n] (first reduces)] [sym n (tags sym)])
          accept (when-let [[sym n] (first accepts)] [sym -1 (tags sym)])]
    (next reduces) 
      (throw (Exception. ^String (apply str "at state " state "\n  reduce/reduce conflict " (interpose "\n" reduces))))
    (and reduction (seq shifts))
      (throw (Exception. (str "at state " state "\n shift/reduce conflict " shifts "\n" reduces)))
    (table-state (matcher (keys shifts)) shifts reduction gotos accept)))

(defn to-states [{:keys [gotos shifts]}]
  (concat (vals gotos) (vals shifts)))

(defn lr-table [[grammar tags matches-empty]]
  (let [grammar (-> grammar (dissoc ::p/S) 
                  (assoc 0 (::p/S grammar)))
        tags (assoc tags 0 (tags ::p/S))
        init-states (u/map-vals grammar #(set (for [prod %2] [%1 (count prod) prod])))
        close (partial close init-states)
        state0 (-> 0 init-states close)
        transitions (partial transitions close tags)
        table (loop [table {} todo #{state0}]
                (if-let [state (first todo)]
                  (let [transition (transitions state)
                        table (assoc table state transition)
                        new-states (remove table (to-states transition))
                        todo (-> todo (disj state) (into new-states))]
                    (recur table todo))
                  table))
        table (assoc table 0 (assoc (table state0) :accept (when matches-empty
                                                             [0 -1 (tags 0)])))
        ; state0 is unreachable by construction
        table (dissoc table state0)]
    table))

(defn- eof-reduction [state]
  (reduce (fn [[mk mn :as best] [k n prod]]
            (let [n (- n (count prod))]
              (if (and best (>= mn n)) best [k n])))
          nil state))

(defn- unfinished-state [public accept n]
  (let [state #{[::p/unfinished (inc n) nil]}
        state-id [::p/unfinished (boolean public) (boolean accept) n]
        transitions (transitions identity (if public #{::p/unfinished} #{}) state)
        transitions (if accept 
                      (assoc transitions :accept [::p/unfinished -1 ::p/unfinished])
                      transitions)]
    [state-id transitions]))

(defn totalize [table]
  ;; I wanted to make table the only input of totalize
  ;; that's why the tags map is recomputed
  (let [tags (into {} (for [transition (vals table)
                            :let [[k _ tag] (or (:reduce transition) (:accept transition))]
                            :when tag] 
                        [k tag]))]
    (reduce 
      (fn [table [state transition]]
        (u/cond
          (:reduce transition)
            table
          (= 0 state)
            (let [table (if-not (:accept transition)
                          (assoc-in table [state :accept] [::p/unfinished -1 ::p/unfinished])
                          table)
                  [ustate utransition :as ust] (unfinished-state (tags 0) true 0)
                  table (assoc-in table [state :gotos ::p/unfinished] ustate)]
              (conj table ust))
          :let [[k n] (eof-reduction state)
                tag (when (tags k) ::p/unfinished)
                [ustate utransition :as ust] (unfinished-state tag (= 0 k) n)]
          (conj table ust
                [state (-> transition
                         (assoc :eof [::p/unfinished n tag])
                         (assoc-in [:gotos ::p/unfinished] ustate))])))
    table table)))

(defn number-states [table]
  (let [table-without-start (dissoc table 0)
        mapping (zipmap (cons 0 (keys table-without-start)) (range))
        renum (fn [m] (reduce #(update-in %1 [%2] mapping) m (keys m)))
        syms (set (for [v (vals table) [x] [(:reduce v) (:eof v) (:accept v)] :when x] x))
        syms-mapping (zipmap syms (range))
        renum-action #(when-let [[sym n tag] %] [(syms-mapping sym) n tag])
        empty-goto (vec (repeat (count syms) nil))
        renum-gotosyms (fn [goto] (reduce (fn [goto [sym state]]
                                            (assoc goto (syms-mapping sym) state))
                                       empty-goto goto))]
    (vec
      (for [{shifts :shifts gotos :gotos :as v} 
            (cons (get table 0) (vals table-without-start))]
        (assoc v :reduce (renum-action (:reduce v))
               :eof (renum-action (:eof v))
               :accept (renum-action (:accept v))
               :shifts (renum shifts) :gotos (-> gotos renum renum-gotosyms)))))
  
)

(comment
    (def g 
      {:E #{["(" :E+ ")"]
            [#"\w+"]}
       :E+ #{[:E+ :E]
             [:E]}})
  
    (let [t (lr-table [g :E identity])]
      (step t zero "((hello)"))
    
)
