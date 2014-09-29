theory Ex5_4
  imports Main
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 5.4:
*)

inductive ev :: "nat \<Rightarrow> bool" where 
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma
  shows "\<not>(ev (Suc (Suc (Suc 0))))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  thus False  proof cases
    case evSS thus False by (induction "Suc 0")
  qed
qed

end

