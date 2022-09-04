(ns cps.core
  (:require [clojure.core.match :refer [match]]
            [schema.core :as s]))

(s/enum :var :fun :app :dif)

(def Exp
  (fn [expression]
    (match
     expression
     [:var v] (s/validate s/Str v)
     [:fun _var _exp] true
     [:app _ _] true
     [:dif _ _ _] true
     )))

(def AbstractArg
  (fn [a]
    (match a
           [:avar var] (s/validate s/Str var)
           [:aclo var exp env]
           (and (s/validate s/Str var)
                (s/validate Exp exp)
                (s/validate Env env)))))

(def Env {s/Str AbstractArg})
(def AbstractContinuation

  (fn [ac]
    (match
     ac
     [:ahalt] true
     [:kvar v] (s/validate s/Str v)
     [:fcont exp env abstractcontinuation] ;;=>
     (and (s/validate Exp exp)
          (s/validate Env env)
          (s/validate AbstractContinuation abstractcontinuation))
     [:acont abstractarg abstractcontinuation]
     (and (s/validate AbstractArg abstractarg)
          (s/validate AbstractContinuation abstractcontinuation))
     [:icont exp0 exp1 env abstractcontinuation]
     (and (s/validate Exp exp0)
          (s/validate Exp exp1)
          (s/validate Env env)
          (s/validate AbstractContinuation abstractcontinuation))
     )   )
  )

(s/set-compile-fn-validation! true)
(defn one-ref [y]
  (and (>= (count y) 1)
       (= (subs y 0 1)
          ":")))

(defn extend_ [y a env]
  (merge env {y a}))

(defn new-count [x counts]
  (assoc counts x 0))

(defn incr [x counts]
  (update counts x inc))

(declare ret)
(s/defn cps [exp :- Exp
             env :- {s/Str Exp}
             c
             counts :- {s/Str s/Int}]
  (match exp
         [:var y] (ret c (find env y) counts)
         [:fun y e] (ret c [:aclo y e env] counts)
         [:app e1 e2] (cps e1 env [:fcont e2 env c] counts)
         [:dif e1 e2 e3] (cps e1 env [:icont e2 e3 env c] counts))
  ;; (condp = (first exp)
  ;;   :var (let [y (second exp)]
  ;;          (ret c (find y env) counts))
  ;;   :fun (let [y (first exp)
  ;;              e (second exp)]
  ;;          (ret c [:aclo y e env] counts))
  ;;   :app (let [[e1 e2] [(first exp) (second exp)]]
  ;;          (cps e1 env [:fcont e2 env c] counts))
  ;;   :dif (let [[e1 e2 e3] [(nth exp 0) (nth exp 1) (nth exp 2)]]
  ;;          (cps e1 env [:icont e2 e3 env c] counts)))
  )

(declare blessc)
(declare bless-abstract-continuation)
(declare call)
(declare cif)

(s/defn ret [c :- AbstractContinuation a counts]
  (match c
         (:or [:ahalt] [:kvar _]) ;=>
         (let [[cont counts2] (blessc c counts)
               [arg counts3] (bless-abstract-continuation a counts2)]
           [[:ret cont arg] counts3])
         [:fcont e env c'] (cps e env [:acont a c'] counts)
         [:acont a' c'] (call a' c' counts)
         [:icont e1 e2 env c'] (cif a e1 e2 c' env counts)))

(defn call [f a c counts]
  (match
   f
   [:avar _] (let [[func counts2] (bless-abstract-continuation f counts)
                   [arg counts3] (bless-abstract-continuation a counts2)
                   [cont counts4] (blessc c counts3)]
               [[:call func arg cont] counts4])
   [:aclo y body env] (if (one-ref y)
                        (cps body (extend_ y a env) c counts)
                        (let [[arg counts2] (bless-abstract-continuation a counts)]
                          (match arg
                                 [:uvar x] (cps body
                                                (extend_ y [:avar x] env)
                                                c
                                                counts2)
                                 [:lam _]
                                 ;; We've got a "let" redex, binding y to a lambda ter: ((FUN y body)
                                 ;; (FUN ...)) We can't reduce this because y has multiple references in
                                 ;; body, which would replicate the (FUN ...) term. So we produce a CPS
                                 ;; "let", encoded as a CONT redex: (RET (CONT x body') (LAM ...)) where
                                 ;; body' is body cps-converted with the original continuation c, and the
                                 ;; (LAM ...) term is the cps-conversion of the (FUN ...) argument.
                                 (let [x (str (gensym "x"))
                                       counts3 (new-count x counts2)
                                       env' (extend_ y [:avar x] env)
                                       [b counts4] (cps body env' c counts3)]
                                   [[:ret [:cont x b] arg] counts4]))))))


(defn cif [a e1 e2 c env counts]
  (match c
         (:or [:ahalt] [:kvar _])       ;=>
         (let [[test counts2] (bless-abstract-continuation a counts)
               [conseq counts3] (cps e1 env c counts2)
               [alt counts4] (cps e2 env c counts3)]
           [[:cif test conseq alt] counts4])

         [(:or :fcont :acont :icont) _] ;=>
         (let [jv (str (gensym "join"))
               [body counts2] (cif a e1 e2 [:kvar jv] env counts)
               [join counts3] (blessc c counts2)]
           [[:letc jv join body] counts3])))

;; Two "blessing functions to render abstract continuations and abstract
;; arguments into actual syntax"
(defn blessc [c counts]
  (match c
         [:ahalt] [[:halt] counts]
         [:kvar kv] [[:cvar kv] counts]
         [(:or :fcont :acont :icont) _] (let [x (str (gensym "x"))
                                              counts2 (new-count x counts)
                                              [body counts3] (ret c [:avar x] counts2)]
                                          [[:cont x body] counts3])))

(s/defn bless-abstract-continuation [a :- AbstractContinuation
                                     counts :- {s/Str s/Int}]
  (println a counts)
  (match a
         [:avar x] [[:uvar x] (incr x counts)]
         [:aclo y body env] (let [x (str (gensym 'y))
                                  k (str (gensym "k"))
                                  env' (extend_ y [:avar x] env)
                                  [b counts'] (cps body
                                                   env'
                                                   [:kvar k]
                                                   (new-count x counts))]
                              ;; The eta-reduction check. Note that we don't have to check reference counts on k, as continuation variables are linear.
                              (match b
                                     [:call f [:uvar x'] [:cvar k']] (if (and (= x x')
                                                                              (= k k')
                                                                              (= (find counts' x)
                                                                                 1))
                                                                       [f counts']
                                                                       [[:lam x k b] counts'])
                                     _ [[:lam x k b] counts']))))

(cps [:var "a"] [] [:ahalt] {})
(s/validate AbstractContinuation nil)
