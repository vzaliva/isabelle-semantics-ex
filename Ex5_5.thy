theory Ex5_5
  imports Main
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 5.5:
*)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  zero: "iter r 0 x x" |
  step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma iter_star :  "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case zero
  show ?case by (rule star.refl)
next
  case step
  then show ?case by (metis star.step)
qed

end
