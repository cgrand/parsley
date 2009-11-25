;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.internal
 "Core interpreter and basic ops -- private, not part of the public API.")

;; an op is a coll [fn & args]

(defmacro op [args context & body]
  `(fn [~@context ~@args] ~@body))

(defmacro flow-op [args context & body]
  `(op ~args [_# ~@context] ~@body))

;;;; op interpreter fn, returns a coll of [events n-or-nil alter-cont]
(defn interpret-op [[f & args] s cont]
  (apply f s cont args))

;;;; interpreter "loop" for 1 state
(defn interpret-ops* 
 "interpret-ops* returns a seq of [data unconsumed-char-count remaining-ops].
  uncomsumed-char-count and remaining-ops are mutually exclusive (either
  uncomsumed-char-count is nol or remaining-ops empty."  
 [f init s ops]
  (let [l (count s)
        step1 (fn step1 [s acc ops]
                (if-let [[op & next-ops] (seq ops)]
                  (mapcat (fn [[events n cont]]
                            (let [acc (f acc events)]
                              (cond
                                (not s) (step1 nil acc cont) ; EOF
                                n (step1 (subs s n) acc cont)
                                :else [[acc nil cont]])))
                    (interpret-op op s next-ops))
                  [[acc (when (seq s) (- l (count s))) nil]]))]                      
    (step1 s init ops)))

(def interpret-ops (partial interpret-ops* into [])) 

(def run-ops (partial interpret-ops* (constantly nil) nil)) 

(defn interpreter-step1 [f s [k acc ops]]
  (for [[acc n cont] (interpret-ops* #(reduce f %1 %2) acc s ops)
        :when (nil? n)]
    [k acc cont]))  

(defn initial-state [ops]
  [[[] nil ops]])

(defn advance-states [states s]
  (for [[events _ ops] states
        [next-events n next-ops :as state] (interpret-ops* into events s ops)
        :when (nil? n)]
    state))

;; interpreter "loop" for "simultaneous" states
(defn interpreter-step [f states s]
  (mapcat (partial interpreter-step1 f s) states))

;;; ops
;; alternative
(def op-alt 
  (flow-op [& ops] [cont] 
    (map (fn [op] [nil 0 (cons op cont)]) ops))) 
  
;; sequence
(def op-cat 
  (flow-op [& ops] [cont]
    [[nil 0 (concat ops cont)]]))

;; start-span & end-span
(def op-events 
  (flow-op [events] [cont] 
    [[events 0 cont]]))

(def op-repeat 
  (flow-op [op] [cont]
    [[nil 0 cont] [nil 0 (list* op [op-repeat op] cont)]]))

;; ref
(def op-ref
  (flow-op [r] [cont]
    [[nil 0 (cons @r cont)]]))
    
(defn- advance-lookahead [op alts s cont]
  (let [ops (if (next alts) [(cons op-alt (map (partial cons op-cat) alts))] (first alts))
        new-lookahead (cons op ops)]
    (for [[events n new-cont] (interpret-ops s cont)]
      (if (= new-cont cont)
        [nil nil (cons new-lookahead new-cont)]
        [events n (cons new-lookahead new-cont)]))))

(def op-lookahead 
  (op [& ops] [s cont]
    (when-let [conts (seq (map #(nth % 2) (run-ops s ops)))]
      (if (some empty? conts)
        [[nil 0 cont]]
        (advance-lookahead op-lookahead conts s cont)))))
  
(def op-negative-lookahead
  (op [& ops] [s cont]
    (if-let [conts (seq (map #(nth % 2) (run-ops s ops)))]
      (when (every? first conts)
        (advance-lookahead op-negative-lookahead conts s cont))
      [[nil 0 cont]])))
        
;; string
(def op-string 
  (op [#^String word] [#^String s cont] 
    (cond
      (nil? s) nil
      (.startsWith s word)
        [[[word] (count word) cont]]
      (.startsWith word s)
        [[[s] nil (cons [op-string (subs word (count s))] cont)]])))

;; char ranges
(def char-range-op 
  (op [ranges] [[c :as s] cont] 
    (cond
      c (let [x (int c)]
          (when-let [max (-> ranges (rsubseq <= x) first second)]
            (when (>= max x) 
              [[[(str c)] 1 cont]])))
      s [[nil nil (cons [char-range-op ranges] cont)]])))


(def op-eof 
  (op [] [s cont] 
    (cond
      (nil? s)
        [[nil nil cont]]
      (= "" s)
        [[nil nil (cons [op-eof] cont)]])))
    
