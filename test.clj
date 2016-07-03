#!/usr/bin/env boot

;; (set-env! :dependencies)
(require '[clojure.pprint :refer (pprint)]
         '[clojure.edn]
         '[clojure.java.shell]
         '[clojure.string])

(def cmd "ghc /home/jano/Work/socql/resources/hs/SelectDSLParser.hs -e main")

;; (-main)

(defn run-test [context {:keys [input output expected nr name]}]
  (let [output (-> ((:evaluator context) input))
        green! (str \u001b "[32m")
        red! (str \u001b "[31m")
        clear! (str \u001b "[0m")
        gray! (str \u001b "[37m")]
    (if (= output expected)
      (do
        (println nr \tab (str green! "✓ " name clear!))
        context)
      (do
        (println nr \tab (str red! "✘ " name clear!))
        (println "input: " gray! input clear!)
        (println "expected: ")
        (print gray!) (pprint expected) (print clear!)
        (println "got: ")
        (print red!) (pprint output) (print clear!)
        (println (str \u001b  "[0m"))
        (-> context
            (update :failed conj nr))))))

(defn -main [& args]
  (println "starting test..")
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
        ask!   (fn [s] (write! s) (read!))
        tests (for [[kname v] (ns-map *ns*)
                    :when (.startsWith (name kname) "test-case-")]
                @v)
        tests (sort-by :nr tests)
        context {:failed [], :evaluator ask!}
        state (reduce run-test context tests)
        ]
    (.destroy proc)
    ;;(println context)
    (when-let [failed (seq (:failed state))]
      (println "FAILED:" (clojure.string/join ", " failed)))
    (println "TOTAL:" (count tests) "tests")
    :ok))

(def -counter (atom 0))

(defmacro testing [name input expected]
  (assert (string? name))
  (swap! -counter inc)
  `(def ~(symbol (str "test-case-" @-counter))
     {:input '~input :expected '~expected :name ~name
      :nr ~(deref -counter)
      }))


                                        ; TEST CASES


(testing "Simple query"
  "SELECT likes FROM fb WHERE id==1"
  {:select {likes likes} :from fb :where (cnf [(== id 1)])})

(testing "Simple query with crazy identifiers"
  "SELECT ga:sessions FROM fb123 WHERE $id==1"
  {:select {ga:sessions ga:sessions}, :from fb123, :where (cnf [(== $id 1)])})

(testing "Simple query with table alias"
  "SELECT fb.likes FROM tablename AS fb WHERE fb.id==1"
  {:select {fb.likes likes} :from tablename :where (cnf [(== id 1)])})

(testing "Simple query with column alias"
  "SELECT likes AS ll FROM fb WHERE id==1"
  {:select {ll likes} :from fb :where (cnf [(== id 1)])})

(testing "Simple query with table alias and column alias"
  "SELECT fb.likes AS ll FROM tablename AS fb WHERE fb.id==1"
  {:select {ll likes} :from tablename :where (cnf [(== id 1)])})

(testing "Simple query with colname in filtering not in selection"
  ;; keys a and b should be introduced in inner selection.
  "SELECT likes FROM facebook WHERE id==1 and a==b"
  {:select {likes facebook/likes},
   :from {facebook
          {:select {likes likes, a a, b b},
           :from facebook, :where (cnf [(== id 1)])}},
   :where (cnf [(== facebook/a facebook/b)])})

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
;; (-main)

(testing "Single subquery"
  "SELECT t.likes FROM (SELECT xx as x, yy as y FROM webpage where id==1) AS t where t.x==t.y"
  {:select {t.likes t/likes},
   :from {t {:select {x xx, y yy},
             :from webpage,
             :where (cnf [(== id 1)])}},
   :where (cnf [(== t/x t/y)])})

(testing "Single subquery with filter inside"
  ;; aa, bb should be moved to the middle query automatically
  "SELECT t.y FROM (SELECT xx as x, yy as y FROM webpage where id==1 and aa==bb) AS t where t.x==t.y"
  {:select {t.y t/y},
   :from {t {:select {x webpage/x, y webpage/y},
             :from {webpage {:select {x xx, y yy, aa aa, bb bb}, :from webpage, :where (cnf [(== id 1)])}},
             :where (cnf [(== webpage/aa webpage/bb)])}},
   :where (cnf [(== t/x t/y)])})
