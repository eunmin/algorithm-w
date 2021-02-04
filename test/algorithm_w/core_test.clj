(ns algorithm-w.core-test
  (:require [clojure.test :refer :all]
            [algorithm-w.core :refer [->ELet ->EAbs ->EVar ->EApp ->ELit ->LInt ->LBool type-inference]])
  (:import [algorithm_w.core TFun TInt TBool]))

(deftest core-test
  (testing "e0"
    (let [exp (->ELet "id" (->EAbs "x"
                                   (->EVar "x"))
                      (->EVar "id"))
          result (type-inference {} exp)]
      (is (instance? TFun result))
      (is (= (:t1 result) (:t2 result)))))

  (testing "e1"
    (let [exp (->ELet "id" (->EAbs "x"
                                   (->EVar "x"))
                      (->EApp (->EVar "id") (->EVar "id")))
          result (type-inference {} exp)]
      (is (instance? TFun result))
      (is (= (:t1 result) (:t2 result)))))

  (testing "e2"
    (let [exp (->ELet "id" (->EAbs "x"
                                   (->ELet "y" (->EVar "x")
                                           (->EVar "y")))
                      (->EApp (->EVar "id") (->EVar "id")))
          result (type-inference {} exp)]
      (is (instance? TFun result))
      (is (= (:t1 result) (:t2 result)))))

  (testing "e3"
    (let [exp (->ELet "id" (->EAbs "x"
                                   (->ELet "y" (->EVar "x")
                                           (->EVar "y")))
                      (->EApp (->EApp (->EVar "id") (->EVar "id")) (->ELit (->LInt 2))))
          result (type-inference {} exp)]
      (is (instance? TInt result))))

  (testing "e4"
    (let [exp (->ELet "id" (->EAbs "x"
                                   (->EApp (->EVar "x") (->EVar "x")))
                      (->EVar "id"))]
      (is (thrown? Exception (type-inference {} exp))) ))

  (testing "e5"
    (let [exp (->EAbs "m"
                      (->ELet "y" (->EVar "m")
                              (->ELet "x" (->EApp (->EVar "y") (->ELit (->LBool true)))
                                      (->EVar "x"))))
          result (type-inference {} exp)]
      (is (instance? TFun result))
      (is (instance? TFun (:t1 result)))
      (is (instance? TBool (:t1 (:t1 result))))
      (is (= (:t2 (:t1 result)) (:t2 result))))))

