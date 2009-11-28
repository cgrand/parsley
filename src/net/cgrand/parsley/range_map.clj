(ns net.cgrand.parsley.range-map)

(defn compare-range [[i j] [k l]]
  (cond
    (<= j k) -1
    (<= l i) 1
    :else 0))

(defn overlap [range-map i j]
  (let [i [i i] j [j j]]
    [(find range-map i)
     (subseq range-map > i < j)
     (find range-map j)]))

(defn assoc-range [range-map i j v]
  (if (< i j)
    (assoc range-map [i j] v)
    range-map))

(defn conj-range [range-map [[from to :as range] value]]
  (let [[a bs c] (apply overlap range-map range)
        range-map (reduce (fn [range-map [k v]]
                            (assoc range-map k (conj v value))) 
                    range-map bs)
        range-map (if-let [[[from-a to-a :as k] v] a]
                    (if (< from-a from)
                      (-> range-map (dissoc k) (assoc [from-a from] v)
                        (assoc [from to-a] (conj v value)))
                      (-> range-map (assoc k (conj v value))))
                    range-map)
        range-map (if-let [[[from-c to-c :as k] v] c]
                    (if (< to to-c)
                      (-> range-map (dissoc k) (assoc [to to-c] v)
                        (assoc [from-c to] (conj v value)))
                      (-> range-map (assoc k (conj v value))))
                    range-map)
        ranges (concat [(if a (key a) [nil from])] 
                 (map key bs) 
                 [(if c (key c) [to nil])])
        spaces (map (fn [[_ to] [from]] [to from]) 
                 ranges (rest ranges))
        singleton #{value}] 
  (reduce #(if (apply < %2)
             (assoc %1 %2 singleton) 
             %1) range-map spaces)))

(defn range-map [& keyvals]
  (reduce conj-range (sorted-map-by compare-range) (partition 2 keyvals)))   


