(ns test
  (:require [clojure.pprint :refer (pprint)]))

(def cmd "ghc /home/jano/Work/socql/resources/hs/SelectDSLParser.hs -e main")

;; (def patterns (atom ()))

(def tests (atom {}))

(defn -main []
  (let [proc   (.exec (Runtime/getRuntime) cmd)
        read!  (let [pbr (->> (.getInputStream proc)
                              (new java.io.InputStreamReader)
                              (new java.io.PushbackReader))]
                 #(clojure.edn/read pbr))
        write! (let [out (.getOutputStream proc)]
                 (fn [s]
                   (assert (string? s))
                   (assert (neg? (.indexOf (str s) "\n")))
                   (.write out (.getBytes (str s)))
                   (.write out 10)
                   (.flush out)))
        ask!   (fn [s] (write! s) (read!))]
    (doseq [[k v] @tests
            :let [output (ask! (:input v))]]
      (if (= output (:expected v))
        (println " ✓ " k)
        (do
          (println (str \u001b "[31m") "✘ "  k)
          (println "input: " (:input v))
          (println "expected: ")
          (pprint (:expected v))
          (println "got: ")
          (pprint output)
          (println (str \u001b  "[0m"))
          )))
    (.destroy proc)))


(defmacro testing [name input expected]
  `(swap! tests assoc ~name {:input '~input, :expected '~expected}))


(testing "Simple query"
  "SELECT likes FROM fb WHERE id==1"
  {:select {likes likes} :from fb :where (cnf [(== id 1)])})

(testing "Simple query with table alias"
  "SELECT fb.likes FROM tablename AS fb WHERE fb.id==1"
  {:select {fb.likes likes} :from tablename :where (cnf [(== id 1)])})

(testing "Simple query with column alias"
  "SELECT likes AS ll FROM fb WHERE id==1"
  {:select {ll likes} :from fb :where (cnf [(== id 1)])})

(testing "Simple query with table alias and column alias"
  "SELECT fb.likes AS ll FROM tablename AS fb WHERE fb.id==1"
  {:select {ll likes} :from tablename :where (cnf [(== id 1)])})

(testing "Simply JOIN two tables with one column alias"
  "SELECT t1.a AS t1a_alias, t2.b FROM t1, t2 WHERE t1.a==t2.b and t1.x==1 and t2.y==2"
  {:select {t1a_alias t1/a, t2.b t2/b}
   :from {t1 {:select {a a}, :from t1, :where (cnf [(== x 1)])},
          t2 {:select {b b}, :from t2, :where (cnf [(== y 2)])}},
   :where (cnf [(== t1/a t2/b)])})


(testing "Simply JOIN two tables on key NOT IN selection of subquery."
  ;; the system should add the missing column name/alias pairs to the subquery select maps.
  "SELECT t1.a, t2.b FROM t1, t2 WHERE t1.x==t2.y and t1.f==1 and t2.g==2"
  {:select {t1.a t1/a, t2.b t2/b}
   :from {t1 {:select {a a, x x} :from t1 :where (cnf [(== f 1)])}
          t2 {:select {b b, y y} :from t2 :where (cnf [(== g 2)])}}
   :where (cnf [(== t1/x t2/y)])})


(-main)
