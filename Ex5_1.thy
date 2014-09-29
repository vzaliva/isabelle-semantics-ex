theory Excercise51
  imports Main
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 5.1:
*)

(* 
  "In the following example, T and A are two binary predicates.  
   It is shown that if T is total, A is antisymmetric and T is a subset of
  A, then A is a subset of T"
*)

theorem
  assumes T: "\<forall> x y . T x y \<or> T y x"
  and A: "\<forall> x y . A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y . T x y \<longrightarrow> A x y" 
  and "A a b"
  shows "T a b"
proof (rule ccontr)
  assume C: "\<not> ?thesis" 
  hence "T b a" using T by fast
  hence "A b a" using TA by simp
  hence "a=b" using A assms(4) by simp
  (* Next step could be skipped: *)
  hence "T a b = T b a" by simp 
  thus False using T by (metis C)
qed





  

