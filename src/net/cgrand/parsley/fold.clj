;   Copyright (c) Christophe Grand. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns net.cgrand.parsley.fold
  (:require [net.cgrand.parsley.util :as u]))

(defprotocol EphemeralFolding
  (unexpected! [this s])
  (node! [this tag n])
  (leaf! [this s])
  (cat! [this pfq]))

; nodes is a collection of nodes (returned by make-node)
; pending is an alternate collection of tag, coll of nodes, integer

(deftype FoldingQueue [^java.util.ArrayList pending ^java.util.ArrayList nodes 
                       ^java.util.ArrayList offsets
                       make-node make-leaf make-unexpected]
  EphemeralFolding
  (unexpected! [this s]
    (when make-unexpected
      (.add nodes (make-unexpected s))
      this))
  (node! [this tag N]
    (let [n (.size offsets)]
      (u/cond 
        (or (> N n) (neg? N))
          (do
            (doto pending
              (.add tag)
              (.add (vec nodes))
              (.add (- N n)))
            (.clear nodes)
            (.clear offsets))
        :let [m (- n N)
              offset (.get offsets m)
              _ (-> offsets (.subList (inc m) n) .clear)]
        tag
          (let [tail (.subList nodes offset (.size nodes))
                children (vec (.toArray tail))]
            (.clear tail)
            (.add nodes (make-node tag children))))
      this))
  (leaf! [this s]
    (let [leaf (if make-leaf (make-leaf s) s)
          offset (.size nodes)]
      (.add offsets offset)
      (.add nodes leaf)
      this))
  (cat! [this pfq]
    (doseq [[tag pnodes n] (partition 3 (:pending pfq))]
      (.addAll nodes pnodes)
      (.node! this tag n))
    (let [n (.size nodes)] 
      (.addAll nodes (:nodes pfq))
      (doseq [offset (:offsets pfq)]
        (.add offsets (+ n offset))))
    this)
  clojure.lang.IDeref
  (deref [this]
    {:pending (vec pending) :nodes (vec nodes) :offsets (vec offsets)
     :make-node make-node :make-leaf make-leaf :make-unexpected make-unexpected}))

(defn folding-queue 
  [{:keys [pending nodes offsets make-node make-leaf make-unexpected]
    :or {pending [] nodes [] offsets []}}] 
  (FoldingQueue. (java.util.ArrayList. ^java.util.Collection pending)
                 (java.util.ArrayList. ^java.util.Collection nodes)
                 (java.util.ArrayList. ^java.util.Collection offsets)
                 make-node make-leaf make-unexpected))

(defn cat [a b]
  @(cat! (folding-queue a) b))

(defn finish [pfq]
  (u/cond
    :let [{:keys [pending nodes offsets make-node]} pfq]
    (and (seq nodes) (seq pending))
      nil
    [[x & xs] (seq nodes)]
      (when-not xs x)
    [[[tag pnodes n] & xs] (seq (partition 3 pending))]
      (when (and (not xs) (neg? n) tag) (make-node tag pnodes))))

(defn stitchability 
  "Returns :full, or a number (the number of states on A stack which remains untouched)
   when rebasing is possible or nil."
 [a b]
  (u/cond
    :let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
    (= a-end b-start) :full
    :let [[a-stack a-rem] a-end
          [b-stack b-rem] b-start]
    :when (= a-rem b-rem)
    :let [b-tail (subvec b-stack b-watermark)
          n (- (count a-stack) (count b-tail))]
    :when (not (neg? n)) 
    (= b-tail (subvec a-stack n)) n))

(defn rebase [b a]
  (u/cond
    :when-let [st (stitchability a b)] 
    (= :full st) b
    ; if it's not full, it's partial
    :let [[a-end] a
          [b-end b-watermark b-events] b
          [a-stack] a-end
          [b-stack b-rem] b-end
          b-tail (subvec b-stack b-watermark)
          a-stub (subvec a-stack 0 st)]
    [[(into (vec a-stub) b-tail) b-rem] st b-events a-end]))

(defn stitch 
 [a b]
  (when (and a b)
    (let [[a-end a-watermark a-events a-start] a
          [b-end b-watermark b-events b-start] b]
      [b-end (min a-watermark b-watermark) (cat a-events b-events) a-start])))
