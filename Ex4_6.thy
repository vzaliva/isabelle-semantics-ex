theory Excercise46
imports
  "~~/src/HOL/IMP/AExp"
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 4.6:
*)

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  n: "aval_rel (N n) s n" |
  v: "aval_rel (V x) s (s x)" |
  p: "\<lbrakk>aval_rel a\<^sub>1 s v\<^sub>1; aval_rel a\<^sub>2 s v\<^sub>2\<rbrakk> \<Longrightarrow> aval_rel (Plus a\<^sub>1 a\<^sub>2) s (v\<^sub>1 + v\<^sub>2)"

lemma aeq1: "aval_rel a s v \<Longrightarrow> (aval a s = v)"
  apply(induction rule: aval_rel.induct)
  apply(auto)
done

lemma aeq2: "((aval a s) = v) \<Longrightarrow> (aval_rel a s v)"
  apply(induction a arbitrary: s v)
  apply(simp_all)
  apply(auto)
  apply(rule aval_rel.n)
  apply(rule aval_rel.v)
  apply(rule aval_rel.p)
  apply(auto)
done

theorem "((aval a s) = v) = (aval_rel a s v)"
  apply(auto)
  apply(rule aeq2)
  apply(simp)
  apply(rule aeq1)
  apply(simp)
done
