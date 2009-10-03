;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.core
 "Core interpreter and basic ops -- private, not part of the public API.")

;; an op is a coll [fn & args]

(defmacro op [args context & body]
  `(fn [~@context ~@args] ~@body))

(defmacro flow-op [args context & body]
  `(op ~args [_# ~@context] ~@body))

;;;; op interpreter fn
(defn interpret-op [[f & args] s cont]
  (apply f s cont args))

;;;; interpreter "loop" for 1 state
(defn interpret-ops* [f init s ops]
  (let [l (count s)
        step1 (fn step1 [s acc ops]
                (if-let [[op & cont] (seq ops)]
                  (mapcat (fn [[events n cont]]
                            (let [acc (f acc events)]
                              (cond
                                (not s) (step1 nil acc cont) ; EOF
                                n (step1 (subs s n) acc cont)
                                :else [[acc nil cont]])))  
                    (interpret-op op s cont))
                  [[acc (when (seq s) (- l (count s))) nil]]))]                      
    (step1 s init ops)))

(def interpret-ops (partial interpret-ops* into [])) 

(def run-ops (partial interpret-ops* (constantly nil) nil)) 

(defn interpreter-step1 [f s [k acc ops]]
  (for [[acc n cont] (interpret-ops* #(reduce f %1 %2) acc s ops)
        :when (nil? n)]
    [k acc cont]))  

;; interpreter "loop" for "simultaneous" states
(defn interpreter-step [f states s]
  (mapcat (partial interpreter-step1 f s states)))

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

(defn- consume [n s]
  (if n (subs s 0 n) s))

(def op-lookahead 
  (op [ops] [s cont]
    (for [[_ n next-ops] (run-ops s ops)]
      (if (seq next-ops)
        (for [[events m next-cont] (interpret-ops (consume n s) cont)
              :when (nil? m)]
          [events n (cons [op-lookahead next-ops] next-cont)])
        [[nil 0 cont]]))))
  
(def op-negative-lookahead
  (op [ops] [s cont]
    (if-let [r (seq (run-ops s ops))]
      (for [[_ n next-ops] r]
        (when (seq next-ops)
          (for [[events m next-cont] (interpret-ops (consume n s) cont)
                :when (nil? m)]
            [events n (cons [op-negative-lookahead next-ops] next-cont)])))
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

(def op-eof 
  (op [] [s cont] 
    (cond
      (nil? s)
        [[nil nil cont]]
      (= "" s)
        [[nil nil (cons [op-eof] cont)]])))
    
