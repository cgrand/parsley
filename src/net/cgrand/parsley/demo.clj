(ns net.cgrand.parsley.demo
  (:use [net.cgrand.parsley
     :only [parser step reset stitch results stitchable?]] :reload))
     
(def simple-lisp 
  (parser {:space #"\s+"
           :main :expr*} 
    :expr #{:symbol ["(" :expr* ")"]}
    :symbol #"\w+"))   

(def clojure-parser 
  (parser {:space #{#"[\s,]+" :comment}
           :main :expr*} 
    :expr #{:list :vector :map :set :fn 
            :meta :with-meta :quote :syntax-quote :unquote :unquote-splice
            :regex :string :number :keyword :symbol :nil :boolean :char}

    :comment #{#"(;|#!)[^\n]*(?=\n)"
               ["#_" :expr]}

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

    :nil "nil"
    :boolean #{"true" "false"}
    ;; todo: refine these terminals
    :char #"\\."
    :symbol #"\w+"
    :keyword #":\w+"
    :number #"\d+"
    :string #"\"[^\"]*\""
    :regex #"#\"[^\"]*\""))

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
;;> ((:main (:expr "(" (:expr (:symbol "bonjour")) (:w " ") (:expr (:symbol "hello")) ")")))

    