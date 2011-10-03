;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.stack)

(defprotocol EphemeralStack
  (push! [this x])
  (popN! [this n])
  (peek! [this]))

(deftype Stack [^java.util.ArrayList list 
                ^{:unsynchronized-mutable true, :tag long} wm]
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
      (set! wm (Math/min (long wm) (long i)))
      (.get list i)))
  clojure.lang.IDeref
  (deref [this]
    {:watermark wm
     :stack (vec list)}))

(defn stack [coll]
  (Stack. (java.util.ArrayList. ^java.util.Collection coll) (count coll)))