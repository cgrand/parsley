;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

;; THIS FILE IS OUT OF DATE

(ns net.cgrand.parsley.demo
  (:use net.cgrand.parsley :reload-all)
  (:require [net.cgrand.parsley.internal :as core]))

;; TRY AT YOUR OWN RISK :-)

(def simple-lisp 
  (grammar {:space [" "+]
            :main [:expr* eof]} 
    :eot- (with #{(one-of "()") eof})
    :expr #{:symbol ["(" :expr* ")"] :nil}
    :nil (token "nil" :eot)
    :symbol (token (but :nil) {\a \z \A \Z \- \-} {\a \z \A \Z \0 \9 \- \-}*)))   

(-> simple-lisp (step "a") count)

(defmulti str-op first)
(defn str-ops [ops] (apply str (interpose " " (map str-op ops)))) 

(defmethod str-op :default [[op]] (str"?" (class op) "?"))
(defmethod str-op core/op-cat [[_ & xs]] (str "[" (str-ops xs) "]"))
(defmethod str-op core/op-alt [[_ & xs]] (str "#{" (apply str (interpose ", " (map str-op xs))) "}"))
(defmethod str-op core/op-string [[_ s]] (pr-str s))
(defmethod str-op core/op-repeat [[_ op]] (str (str-op op) "*"))
(defmethod str-op core/op-lookahead [[_ & ops]] (str "(with " (str-ops ops) ")"))
(defmethod str-op core/op-negative-lookahead [[_ & ops]] (str "(but " (str-ops ops) ")"))

;(doseq [[_ _ x] (reduce step clojure-parser (take 10 selfs))] (println (str-ops x)))

(defn copy [x] (-> (java.awt.Toolkit/getDefaultToolkit) .getSystemClipboard (.setContents (java.awt.datatransfer.StringSelection. (str x)) nil)))

(defn str-cont [[_ _ cont]] (str-ops cont))
(defn str-conts [x] (map str-cont x))
(defn prn-conts [xs]
  (doseq [x xs] (println (str-cont x))))

(require '[net.cgrand.parsley.glr :as core])
(use 'net.cgrand.parsley :reload-all)

(def sexp 
  (grammar {:space :whitespace?
            :main [:expr*]}
    :expr- #{:atom :list :vector :set :map}
    :atom (token {\a \z \A \Z \- \- \0 \9 \. \.}+ (?! {\a \z \A \Z \- \- \0 \9 \. \.}))
    :list ["(" :expr* ")"]
    :vector ["[" :expr* "]"]
    :set ["#{" :expr* "}"]
    :map ["{" :expr* "}"]
    
    :whitespace (token #{\space \tab \newline}+ (?! #{\space \tab \newline}))))  

(def table (apply core/lr-table sexp))
(def sop [[(list 0) () nil]])

(defn bench[n]
  (let [s "(defn fast-tables [table]
  (let [fast-rows (map fast-row table)]
    [(to-array (map first fast-rows))
     (to-array (map second fast-rows))]))"
        s (apply str (repeat n s))]
    (println "parsing" (count s) "chars")
    (time (-> sop (core/step table s) count))))

(defn bench2[n]
  (let [s "(defn fast-tables [table]
  (let [fast-rows (map fast-row table)]
    [(to-array (map first fast-rows))
     (to-array (map second fast-rows))]))"
        s (apply str (repeat n s))]
    (println "parsing" (count s) "chars")
    (time (-> sop (core/step table s) first second (core/read-events s)))))

(-> sop (core/step table "hello"))

(def g
  (grammar {:space [#{:white-space #_:comment :discard}*]
            :main [:expr*]}

    :terminating-macro- (one-of "\";']^`~()[]{}\\%")
    :macro- #{:terminating-macro (one-of "@#")}
    :space- (one-of " \t\n\r,")
    
    :token- (token {\a \z}+ (?= #{:terminating-macro :space $}))
    :white-space (token :space+ (?! :space))  
    ;:comment (token #{";" "#!"} (not-one-of "\n")*) 
    :discard ["#_" :expr]
    
    :expr #{:list :vector :map :set :fn 
            :meta :with-meta :quote :syntax-quote :unquote :unquote-splice
            :regex :string :number :keyword :symbol #_:nil #_:boolean :char}

    :list ["(" :expr* ")"] 
    :vector ["[" :expr* "]"] 
    :map ["{" [:expr :expr]* "}"]
    :set ["#{" :expr* "}"]
    :fn ["#(" :expr* ")"]

    :meta ["^" :expr]
    :with-meta ["#^" :expr :expr]
    :quote ["'" :expr] 
    :syntax-quote ["`" :expr]
    :unquote ["~" :expr]
    :unquote-splice ["~@" :expr]
    :deref ["@" :expr]
    :var ["#'" :expr]

   ; :nil (token "nil" (?! :token-char))
   ; :boolean (token #{"true" "false"} (?! :token-char))
    ;; todo: refine these terminals
    :char (token \\ any-char)
#_(
    :namespace- (token (not-one-of "/" {\0 \9}) :token-char*? "/")
    :name- (token (not-one-of "/" {\0 \9}) [(?! "/") :token-char]*)
    :symbol (token  
              #{["%" :token-char*]
                ["%&"]
                ["/" (?! :token-char)]
                ["clojure.core//" (?! :token-char)]
                [(?! :macro :nil :boolean ":") :namespace? :name]})
                
    :keyword (token (?= ":") :namespace? :name)
)
    :keyword (token \: :token) 
    :symbol (token :token) 

    :number (token {\0 \9}+)

#_(    
    :string (token \" #{[(?! \" \\) any-char] [\\ any-char]}* \")
    :regex (token "#\"" #{[(?! \" \\) any-char] [\\ any-char]}* \")
 )
    :string (token \" {\a \z}* \")
    :regex (token "#\"" {\a \z}* \")))
(def table (apply core/lr-table g))
(def ttable (first table))
(def sop [[[(second table)] [] nil]])

(def red (memoize (fn [n] (if (neg? n) clojure-parser (-> (red (dec n)) (step (nth selfs n)))))))   
(def test-comment
  (grammar {:main :expr* :space [(one-of " \t\n\r,")+]}
    :expr [:line :comment]
    :line [[(but ";") {\a \z}]*]
    :comment (token ";" [(but "\n") any-char]*)))  

(-> test-comment (step "a ;b\nc;d") (step nil) results (->> (map #(apply str (e/emit* %)))))

(defn find-error [s g]
  (loop [seen [] s s p g]
    (if (empty? p)
      (apply str seen)
      (when-let [[c & s] (seq s)]
        (recur (conj seen c) s (step p (str c)))))))
  
  if (and (seq s) (-> f (step s) count zero?))
    (let [i (quot (count s) 2)
          s1 (subs s 0 i)
          s2 (subs s i)
          ]
      (if (-> f (step s1) count zero?)
        
        
      
    

;; helper functions to display results in a more readable way 
(defn terse-result [items]
  (map (fn self [item]
         (if (map? item)
           (cons (:tag item) (map self (:content item)))
           item)) items))

(defn prn-terse [results]
  (doseq [result results]
    (prn (terse-result result))))
    
;; let's parse this snippet
(-> simple-lisp (step "()(hello)") (step nil) results prn-terse)
;;> ((:main (:expr "()") (:expr "(" (:expr (:symbol "hello")) ")")))

;; let's parse this snippet in two steps
(-> simple-lisp (step "()(hel") (step "lo)") eof results prn-terse)
;;> ((:main (:expr "()") (:expr "(" (:expr (:symbol "hello")) ")")))

;; and now, the incremental parsing!
(let [c1 (-> simple-lisp reset (step "()(hel"))
      c2 (-> c1 reset (step "lo)" nil))
      _ (-> (stitch c1 c2) eof results prn-terse) ; business as usual
      c1b (-> simple-lisp reset (step "(bonjour)(hel")) ; an updated 1st chunk
      _ (-> (stitch c1b c2) eof results prn-terse) 
      c1t (-> simple-lisp reset (step "(bonjour hel")) ; an updated 1st chunk
      _ (-> (stitch c1t c2) eof results prn-terse)] 
  nil)
;;> ((:main (:expr "()") (:expr "(" (:expr (:symbol "hello")) ")")))
;;> ((:main (:expr "(" (:expr (:symbol "bonjour")) ")") (:expr "(" (:expr (:symbol "hello")) ")")))
;;> ((:main (:expr "(" (:expr (:symbol "bonjour")) (:w " ") (:expr (:symbol "hello")) ")")))

    