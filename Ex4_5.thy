theory Excercise45 
  imports Main
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 4.5:

by: Vadim Zaliva with help from Jeremy Johnson
*)

(* terminals *)
datatype alpha = a | b 

(* empty word defintion.
NB: This is syntactic sugar. We might as well used [] in the contexts where the type of [] could be derived automaticlaly *)
definition \<epsilon> :: "alpha list" where "\<epsilon>=[]"

inductive S :: "(alpha list) \<Rightarrow> bool" where
  empty: "S \<epsilon>"
  | paren: "S w \<Longrightarrow> S (a # w @ [b])"
  | repeat: "\<lbrakk>S x; S y \<rbrakk> \<Longrightarrow> S (x@y)"

inductive T :: "(alpha list) \<Rightarrow> bool" where
  empty: "T \<epsilon>"
  | interleave: "\<lbrakk>T x; T y \<rbrakk> \<Longrightarrow> T (x@[a]@y@[b])"

lemma TS : "T w \<Longrightarrow> S w "
  apply(induction rule: T.induct)
  apply(rule S.empty)
  apply(rule S.repeat)
  apply(simp)
  apply(simp)
  apply(rule S.paren)
  apply(simp)
done

lemma T01: "T (a#w@[b]) = T (\<epsilon> @ [a] @ w @ [b])"
  apply(simp add: \<epsilon>_def)
done

lemma simpTI : "T (x @ a # y @ [b]) = T (x @ [a] @ y @ [b])"
  apply(auto)
done
 

lemma Tgroup : "T(x1 @ x2 @ [a] @ y @ [b]) = T((x1 @ x2) @ [a] @ y @ [b])"
apply (auto)
done

lemma Tconcat : "\<lbrakk>T w2; T w1 \<rbrakk> \<Longrightarrow> T (w1 @ w2)"
apply (induction rule: T.induct)
apply(simp add: \<epsilon>_def)
apply (simp only: Tgroup)
apply (rule T.interleave)
apply (auto)
done

lemma ST : "S w \<Longrightarrow> T w"
apply (induction rule: S.induct)
apply (rule T.empty)
apply (simp only: T01)
apply (rule T.interleave)
apply (rule T.empty)
apply(simp add: \<epsilon>_def)
apply (simp only: Tconcat) 
done

theorem eqST : "S w = T w "
  apply(auto)
  apply(rule ST)
  apply(simp)
  apply(rule TS)
  apply(simp)
done


end
