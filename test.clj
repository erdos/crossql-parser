#!/usr/bin/env boot

;; (set-env! :dependencies)
(require '[clojure.pprint :refer (pprint)]
         '[clojure.edn]
         '[clojure.java.shell]
         '[clojure.string])

(def cmd "ghc SelectDSLParser.hs -e main")

;; (-main)

(defmacro timer [expr]
  `(let [t1# (System/currentTimeMillis)
         x# ~expr
         t2# (System/currentTimeMillis)]
     {:value x#, :delta (- t2# t1#)}))

(defn run-test [context {:keys [input expected nr name]}]
  (let [{:keys [value delta]} (-> input ((:evaluator context)) (timer))
        green! (str \u001b "[32m")
        red! (str \u001b "[31m")
        cyan! (str \u001b "[36m")
        clear! (str \u001b "[0m")
        gray! (str \u001b "[37m")]

    (if (= value expected)
      (do
        (println nr \tab (str green! "✓ " name clear!) (str delta "ms"))
        context)
      (do
        (println)
        (println nr \tab (str red! "✘ " name clear!) (str delta "ms"))
        (println (str gray! "input: ") cyan! input clear!)
        (println (str gray! "expected: "))
        (print cyan!) (pprint expected) (print clear!)
        (println (str gray! "got: "))
        (print red!) (pprint value) (print clear!)
        (println clear!) (println)
        (-> context
            (update :failed conj nr)
            (update :total  inc))))))

(def -counter (atom 0))

(defmacro testing [name input expected]
  (assert (string? name))
  (swap! -counter inc)
  `(def ~(symbol (str "test-case-" @-counter))
     {:input '~input :expected '~expected :name ~name :nr ~(deref -counter)}))

(defn test-cases []
  (sort-by :nr
    (for [[kname v] (ns-map *ns*) :when (.startsWith (name kname) "test-case-")] @v)))

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
        state (reduce run-test {:failed [], :evaluator ask!, :total 0} (test-cases))]
    (.destroy proc)
    ;;(println context)
    (when-let [failed (seq (:failed state))]
      (println "FAILED:" (clojure.string/join ", " failed)))
    (println "TOTAL:" (:total state) "tests")
    :ok))


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


;; FEATURE: all kinds of relations
(testing "Simple query with all kinds of relations"
  "SELECT id FROM t WHERE a==1 and b<=2 and c>=3 and d<4 and e>5 and f!=6 and g<>7 and h BETWEEN 8 and 9"
  {:select {id id}, :from t,
   :where
   (cnf [(< d 4)] [(> e 5)] [(== a 1)] [(>= c 3)] [(>= h 8)] [(<= b 2)] [(<= h 9)] [(!= f 6)] [(!= g 7)])})


;; FEATURE: conditions propagate over equivalences to submaps.
(testing "Two simple subquery share the same interval"
  "SELECT t1.id, t2.id from t1, t2 where t1.day==t2.weekDay and t1.day between 1 and 7"
  {:select {t1.id t1/id, t2.id t2/id},
   :from {t1 {:select {day day, id id},
              :from t1,
              :where (cnf [(>= day 1)] [(<= day 7)])},
          t2 {:select {weekDay weekDay, id id},
              :from t2,
              :where (cnf [(>= weekDay 1)] [(<= weekDay 7)])}},
   :where (cnf [(== t1/day t2/weekDay)])})


(testing "Simple scalar expression evaluation"
  "SELECT id FROM table WHERE seconds==24*60*60"
  {:select {id id}
   :from table
   :where (cnf [(== seconds 86400)])})


(testing "Two subquery as select expressions"
  "Select x.id, y.id From (SELECT id from t where id > 1) As x, (SELECT id from t where id > 10) As y Where x.id==y.id"
  {:select {x.id x/id, y.id y/id},
   :from {x {:select {id id}, :from t, :where (cnf [(> id 1)])},
          y {:select {id id}, :from t, :where (cnf [(> id 10)])}},
   :where (cnf [(== x/id y/id)])})


(testing "Two subquery as select expressions w alias"
  "Select x.xid, y.yid From (SELECT id As xid from t where id > 1) As x, (SELECT id As yid from t where id > 10) As y Where x.xid==y.yid"
  {:select {x.xid x/xid, y.yid y/yid},
   :from {x {:select {xid id}, :from t, :where (cnf [(> id 1)])},
          y {:select {yid id}, :from t, :where (cnf [(> id 10)])}},
   :where (cnf [(== x/xid y/yid)])})


(testing "Two subquery - one table name, one subexpr"
  "Select x.xid, y.yid From (SELECT id As xid from t where id > 1) As x, y As y Where x.xid==y.yid and y.yid > 12"
  {:select {x.xid x/xid, y.yid y/yid},
   :from {x {:select {xid id}, :from t, :where (cnf [(> id 1)] [(> id 12)])},
          y {:select {yid yid}, :from y, :where (cnf [(> yid 12)])}},
   :where (cnf [(== x/xid y/yid)])})


(testing "One nested select without join expression"
  "SELECT id FROM (SELECT id FROM t where day>2) WHERE id>5"
  {:select {id id}
   :from t
   :where (cnf [(> day 2)] [(> id 5)])})


;; FAILS
(testing "One nested select with alias without join expression"
  "SELECT p.id FROM (SELECT id FROM t where day>2) AS p WHERE p.id>5"
  {:select {id id}
   :from t
   :where (cnf [(> day 2)] [(> id 5)])})


(testing "One nested select with outside only join expr"
  "SELECT id FROM (SELECT id, key FROM t where day>2) WHERE id==key"
  {:select {id $/id}
   :from {$ {:select {id id, key key}
             :from t
             :where (cnf [(> day 2)])}}
   :where (cnf [(== $/id $/key)])})


(testing "One nested select with outside only join expr"
  "SELECT p.id FROM (SELECT id, key FROM t where day>2) AS p WHERE p.id==p.key"
  {:select {p.id p/id}
   :from {p {:select {id id, key key} :from t :where (cnf [(> day 2)])}}
   :where (cnf [(== p/id p/key)])})


(testing "One nested select with join expression and filter on outside"
  "SELECT id FROM (SELECT id, key FROM t where day>2) WHERE id>5 and id==key"
  {:select {id $/id},
   :from
   {$ {:select {id id, key key},
       :from t,
       :where (cnf [(> day 2)] [(> id 5)] [(> key 5)])}},
   :where (cnf [(== $/id $/key)])}  )

(testing "One nested select with join expression and filter on outside"
  "SELECT id FROM (SELECT id, key, aa FROM t where day>2) WHERE aa>5 and id==key"
  {:select {id $/id},
   :from {$ {:select {aa aa, id id, key key},
             :from t,
             :where (cnf [(> aa 5)] [(> day 2)])}},
   :where (cnf [(== $/id $/key)])} )

(testing "Like prev but with table alias."
  "SELECT t.id FROM (SELECT id, key, aa FROM t where day>2) AS t WHERE t.aa>5 and t.id==t.key"
  {:select {t.id t/id},
   :from {t {:select {aa aa, id id, key key},
             :from t,
             :where (cnf [(> aa 5)] [(> day 2)])}},
   :where (cnf [(== t/id t/key)])})

(testing "Nested deep"
  "SELECT id FROM (SELECT a, id FROM (SELECT a, id FROM t WHERE b==1) WHERE a>2) WHERE id>3"
  nil)

(testing "Nested deep"
  "SELECT id FROM (SELECT a, id FROM (SELECT a, id FROM t WHERE b==1 and c==d) WHERE a>2) WHERE id>3"
  nil)

(testing "Nested deep moves join guard outside, filters inside."
  "SELECT id FROM (SELECT a, id FROM (SELECT a, id FROM t WHERE b==1) WHERE a>2 and a<id) WHERE id>3"
  {:select {id $/id}
   :from {$ {:select {id id}
             :from t
             :where (cnf [(> a 2)] [(== b 1)] [(> id 3)])}}
   :where (cnf [(< $/a $/id)])})
