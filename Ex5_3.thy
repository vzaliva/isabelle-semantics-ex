theory Excercise53
  imports Main
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 5.3:
*)

inductive ev :: "nat \<Rightarrow> bool" where 
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma 
  assumes a: "ev (Suc (Suc n))"
  shows "ev n"
using a
proof cases
  case evSS thus "ev n" by simp
qed


end


