(ns net.cgrand.parsley.test
  (:require [net.cgrand.parsley.glr :as core] :reload)
  (:use net.cgrand.parsley :reload)
  (:use clojure.test))

(def sexp
  (let [digits "0123456789"
        spaces " \t\n,"
        terminating-macros "\";'@^`~()[]{}\\%"]
  (parser {:space [#{:whitespace :comment :discard}:*]
            :main :expr*}
    :atom1st- #{{\a \z \A \Z \0 \9} (any-of "!$%&*+-./:<=>?_")}
    :expr- #{:atom :list :vector :set :map :string :regex :broken-map
             :meta :deprecated-meta :quote 
             :unquote :syntax-quote :unquote-splicing
             :deref :var :fn :char}
    :eot- #{(any-of terminating-macros spaces) $} 
    :hex- {\0 \9 \a \f \A \F}
    :atom- (token #{:number :symbol :keyword} (?= :eot))
    :integer- (token #{\+ \-}:? 
                #{\0 
                  [{\1 \9}{\0 \9}:*]
                  [\0 {\X \x} :hex+]
                  [\0 {\0 \7}:+]
                  [{\1 \9}{\0 \9}:? #{\r \R} {\0 \9 \a \z \A \Z}]})
    :ratio- (token #{\+ \-}:? {\0 \9}:+ "/"  {\0 \9}:+)
    :mantissa- (token {\0 \9}:+ (?= (any-of ".eEM")))
    :float- (token #{\+ \-}:? :mantissa ["." {\0 \9}:*]:?
              [#{\e \E} #{\+ \-}:? {\0 \9}:+]:?
              "M":?)
    :number #{:integer :float :ratio}
    :symbol #{"/" "clojure.core//" "+" "-"
              (token 
                #{(none-of "/:#+-" terminating-macros spaces digits) 
                  [(any-of "+-") (none-of digits terminating-macros spaces)]
                  "%"} 
                [(none-of terminating-macros spaces):*
                 (none-of "/" terminating-macros spaces)]:?)}
    :keyword (token \: (none-of "/" terminating-macros spaces)
                [(none-of terminating-macros spaces):*
                 (none-of "/" terminating-macros spaces)]:?)
    :string (token \" #{(none-of \\ \") [\\ any-char]}:* \")
    :char (token \\ #{any-char "newline" "space" "tab" "backspace" 
                      "formfeed" "return"
                      [\u :hex :hex :hex :hex]
                      [\o {\0 \7}]
                      [\o {\0 \7} {\0 \7}]
                      [\o {\0 \3} {\0 \7} {\0 \7}]}
            (?! #{:atom1st \#}))
    :regex (token \# \" #{(none-of \\ \") [\\ any-char]}:* \") 
    :list ["(" :expr* ")"]
    :vector ["[" :expr* "]"]
    :set ["#{" :expr* "}"]
    :map ["{" [:expr :expr]:* "}"]
    :broken-map ["{" [:expr :expr]:* :expr "}"]
    :discard ["#_" :expr]
    :meta ["^" :expr :expr]
    :quote [\' :expr] 
    :syntax-quote [\` :expr]
    :tilda- [\~ (?! \@)]
    :unquote [:tilda :expr]
    :unquote-splicing ["~@" :expr]
    :deprecated-meta ["#^" :expr :expr]
    :deref [\@ :expr]
    :var ["#'" :expr]
    :fn ["#(" :expr* ")"]

    :comment (token #{"#!" ";"} (none-of \newline):* (?! (none-of \newline)))
    
    :whitespace (token (any-of spaces):+ (?! (any-of spaces))))))

(defn step-> [& chunks]
  (let [pieces (reductions sexp nil (concat chunks [nil]))]
    (reduce core/stitch pieces)))

(defn step-> [& chunks]
  (let [pieces (reductions sexp nil (concat chunks [nil]))]
    (reduce (comp doall core/stitch) pieces)))

(defn step-> [& chunks]
  (loop [pieces (reductions sexp nil (concat chunks [nil]))]
    (if (next pieces)
      (recur (map #(if (next %) (apply core/stitch %) (first %)) (partition-all 2 pieces)))
      (first pieces))))

(defn build-tree [pieces]
  (if (next pieces)
    (recur (map #(if (next %) (apply core/stitch %) (first %)) (partition-all 2 pieces)))
    (first pieces)))


(defn tree [parse-tree]
  (cond
    (map? parse-tree) 
      (into [(:tag parse-tree)] (->> parse-tree :content (map tree)))
    (sequential? parse-tree)
      (vec (map tree parse-tree)) 
    :else parse-tree))

(defn match-type [state]
  (case (count state) 0 :fail 1 :match :matches))

(deftest one-chunk
  (are [r s] (= r (match-type (step-> s)))
    :match ""
    :match "hello"
    :match "hello world"
    :match "  hello  "
    :match "(hello)"
    :match "(  hello  )"
    :match "(hello world)"
    :match "(eq r (parse-count table s))"
    :fail "(eq r [parse-count table s))"
    :fail "(eq r (parse-count table s)"))

(deftest chunked
  (are [r ss] (= r (match-type (eof (reduce step sop ss))))
    :match ["" ""]
    :match ["hel" "lo"]
    :match ["  he" "llo  "]
    :match ["(hel" "lo)"]
    :match ["(  hello" "  )"]
    :match ["(hello w" "orld)"]
    :match ["(eq r (parse-count " "table s))"]
    :fail ["(eq r [parse-count " "table s))"]
    :fail ["(eq r (parse-count " "table s)"]))

(deftest one-tree
  (are [s pt] (= pt (-> (step-> s) first second tree))
    "(eq r (parse-count table s))"
      [[:list "(" [:atom "eq"] [:whitespace " "] [:atom "r"] [:whitespace " "] 
         [:list "(" [:atom "parse-count"] [:whitespace " "] [:atom "table"]
           [:whitespace " "] [:atom "s"] ")"] ")"]]
    "[a {b c}(d e)#{f}]"
      [[:vector "[" [:atom "a"] [:whitespace " "] 
         [:map "{" [:atom "b"] [:whitespace " "] [:atom "c"] "}"]
         [:list "(" [:atom "d"] [:whitespace " "] [:atom "e"] ")"]
         [:set "#{" [:atom "f"] "}"]
         "]"]]
      
      ))

(deftest fold-nodes
  (are [in n out]
    (= (core/fold-nodes "clojure" in n) out)
    [1] 1 [[0] ["e"] 6] 
    [2] 1 [[1] ["e"] 6]
    [7] 7 [[0] ["clojure"] 0]
    [7] 8 [["clojure"] nil 8]
    [4 [nil 2 :bar] 3] 5 
      [[1] ["l" {:tag :bar, :content ["oj"]} "ure"] 1]
    [[nil 2 nil] 1 [nil 2 nil] 1 [nil 2 nil] [nil 2 :atom]] 3
      [["re" [nil 5 :atom]] nil 3]
    [1 [nil 2 nil] [nil 2 :atom]] 3
      [["e" [nil 3 :atom]]  nil 3]
    [1 [nil 2 nil] 1 [nil 2 nil] [nil 2 :atom]] 3
      [["re" [nil 4 :atom]] nil 3]))

(deftest read-events
  (is (= (core/read-events [1 1 [nil 4 :atom] 1] "ld)")
        ["ld" [nil 4 :atom] ")"]))
  (is (= (core/read-events [1 [nil 2 nil] 1 [nil 2 nil] [nil 1 :atom] 1] "ld)")
        ["ld" [nil 3 :atom] ")"]))
  (is (= (core/read-events [[nil 2 nil] 1 [nil 2 nil] 1 [nil 2 nil] [nil 2 :atom] 1] "ld)")
        ["ld" [nil 5 :atom] ")"]))
  (is (= (core/read-events [[nil 2 nil] 1 [nil 2 nil] 1 [nil 2 nil] [nil 2 :atom] [nil 3 nil] 1] "ld)")
        ["ld" [nil 5 :atom] [nil 3 nil] ")"]))
  (is (= (core/read-events [4 [3 3 nil]] "(eq a")
        '["e" {:tag nil, :content ("q a")}]))
  )

