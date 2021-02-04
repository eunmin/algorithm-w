(ns algorithm-w.core
  (:require [clojure.set :as set]))

(defprotocol Exp)
(defrecord EVar [s] Exp)
(defrecord ELit [l] Exp)
(defrecord EApp [e1 e2] Exp)
(defrecord EAbs [s e] Exp)
(defrecord ELet [s e1 e2] Exp)

(defprotocol Lit)
(defrecord LInt [x] Lit)
(defrecord LBool [x] Lit)

(defprotocol Type)
(defrecord TVar [n] Type)
(defrecord TInt [] Type)
(defrecord TBool [] Type)
(defrecord TFun [t1 t2] Type)

(defrecord Scheme [vars t])

;; env: {s Scheme}
(defrecord TypeEnv [env])

(defmulti ftv type)

(defmethod ftv :default [_] #{})
(defmethod ftv TVar [{:keys [n]}] #{n})
(defmethod ftv TFun [{:keys [t1 t2]}] (set/union (ftv t1) (ftv t2)))
(defmethod ftv Scheme [{:keys [vars t]}] (set/difference (ftv t) (set vars)))
(defmethod ftv clojure.lang.PersistentVector [t] (reduce #(set/union %1 %2) #{} (mapv ftv t)))
(defmethod ftv TypeEnv [{:keys [env]}] (ftv (vec (vals env))))

(defmulti apply-subst (fn [_ t] (type t)))

(defmethod apply-subst :default [_ t] t)
(defmethod apply-subst TVar [subst t] (or (get subst (:n t)) t))
(defmethod apply-subst TFun [subst {:keys [t1 t2]}] (->TFun (apply-subst subst t1) (apply-subst subst t2)))
(defmethod apply-subst Scheme [subst {:keys [vars t]}] (->Scheme vars (apply-subst (reduce #(dissoc %1 %2) subst vars) t)))
(defmethod apply-subst clojure.lang.PersistentVector [subst t] (mapv #(apply-subst subst %) t))
(defmethod apply-subst TypeEnv [subst {:keys [env]}] (->TypeEnv (into {} (mapv (fn [[k v]] [k (apply-subst subst v)]) env))))

(def null-subst {})

(defn compose-subst [s1 s2]
  (merge s1 (into {} (mapv (fn [[k v]] [k (apply-subst s1 v)]) s2))))

(defn remove-type-env [{:keys [env]} var]
  (->TypeEnv (dissoc env var)))

(defn generalize [type-env t]
  (->Scheme (vec (set/difference (ftv t) (ftv type-env))) t))

(defn new-ty-var []
  (->TVar (str (gensym "var"))))

(defn instantiate [{:keys [vars t]}]
  (apply-subst (zipmap vars (mapv (fn [_] (new-ty-var)) vars)) t))

(defn var-bind [u t]
  (cond
    (= t (->TVar u)) null-subst
    (contains? (ftv t) u) (throw (ex-info "occurs check fails" {:u u :t t}))
    :else {u t}))

(defmulti mgu #(vector (type %1) (type %2)))

(defmethod mgu :default [t1 t2]
  (cond
    (instance? TVar t1) (var-bind (:n t1) t2)
    (instance? TVar t2) (var-bind (:n t2) t1)
    :else (throw (ex-info "types do not unify" {:t1 t1 :t2 t2}))))

(defmethod mgu [TFun TFun] [t1 t2]
  (let [s1 (mgu (:t1 t1) (:t1 t2))
        s2 (mgu (apply-subst s1 (:t2 t1)) (apply-subst s1 (:t2 t2)))]
    (compose-subst s1 s2)))

(defmethod mgu [TInt TInt] [_ _] null-subst)

(defmethod mgu [TBool TBool] [_ _] null-subst)

(defn ti-lit [_ l]
  (cond
    (instance? LInt l) [null-subst (->TInt)]
    (instance? LBool l) [null-subst (->TBool)]))

(defmulti ti (fn [_ e] (type e)))

(defmethod ti EVar [{:keys [env]} {:keys [s]}]
  (if-let [sigma (get env s)]
    [null-subst (instantiate sigma)]
    (throw (ex-info "unbound variable" {:s s}))))

(defmethod ti ELit [type-env {:keys [l]}]
  (ti-lit type-env l))

(defmethod ti EAbs [type-env {:keys [s e]}]
  (let [tv (new-ty-var)
        {:keys [env]} (remove-type-env type-env s)
        env2 (->TypeEnv (merge {s (->Scheme [] tv)} env))
        [s1 t1] (ti env2 e)]
    [s1 (->TFun (apply-subst s1 tv) t1)]))

(defmethod ti EApp [type-env {:keys [e1 e2]}]
  (let [tv (new-ty-var)
        [s1 t1] (ti type-env e1)
        [s2 t2] (ti (apply-subst s1 type-env) e2)
        s3 (mgu (apply-subst s2 t1) (->TFun t2 tv))]
    [(compose-subst (compose-subst s3 s2) s1) (apply-subst s3 tv)]))

(defmethod ti ELet [type-env {:keys [s e1 e2]}]
  (let [[s1 t1] (ti type-env e1)
        {:keys [env]} (remove-type-env type-env s)
        t (generalize (apply-subst s1 type-env) t1)
        env2 (->TypeEnv (assoc env s t))
        [s2 t2] (ti (apply-subst s1 env2) e2)]
    [(compose-subst s1 s2) t2]))

(defn type-inference [env e]
  (let [[s t] (ti (->TypeEnv env) e)]
    (apply-subst s t)))

