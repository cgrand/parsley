(ns net.cgrand.parsley.stack)

(defprotocol EphemeralStack
  (push! [this x])
  (popN! [this n])
  (peek! [this]))

(deftype Stack [^java.util.ArrayList list ^:unsynchronized-mutable ^long wm]
  EphemeralStack
  (push! [this x]
    (.add list x)
    this)
  (popN! [this n]
    (let [sz (.size list)
          sl (.subList list (- sz (long n)) sz)]
      (.clear sl)
      this))
  (peek! [this]
    (let [i (unchecked-dec (.size list))] 
      (set! wm (Math/min wm i))
      (.get list i)))
  clojure.lang.IDeref
  (deref [this]
    {:watermark wm
     :stack (vec list)}))

(defn stack [coll]
  (Stack. (java.util.ArrayList. ^java.util.Collection coll) (count coll)))