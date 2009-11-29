(ns net.cgrand.parsley.range-map.test
  (:require [net.cgrand.parsley.range-map :as rm])
  (:use [clojure.test :only [deftest is are]]))
  
(deftest test-assoc
  (are [expr expected] (= expr expected)
    (rm/range-map) {} 
    (rm/range-map [0 32] :a) {[0 32] #{:a}} 
    (rm/range-map [0 32] :a [64 128] :b) {[0 32] #{:a} [64 128] #{:b}} 
    (rm/range-map [64 128] :b [0 32] :a) {[0 32] #{:a} [64 128] #{:b}} 
    (rm/range-map [0 32] :a [64 128] :b [32 64] :c) 
      {[0 32] #{:a} [32 64] #{:c} [64 128] #{:b}} 
    (rm/range-map [0 32] :a [64 128] :b [31 64] :c) 
      {[0 31] #{:a} [31 32] #{:a :c} [32 64] #{:c} [64 128] #{:b}} 
    (rm/range-map [0 32] :a [64 128] :b [32 66] :c) 
      {[0 32] #{:a} [32 64] #{:c} [64 66] #{:b :c} [66 128] #{:b}} 
    (rm/range-map [0 32] :a [64 128] :b [-4 130] :c) 
      {[-4 0] #{:c} [0 32] #{:a :c} [32 64] #{:c} [64 128] #{:b :c} [128 130] #{:c}})) 

