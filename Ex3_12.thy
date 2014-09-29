theory Ex3_12
imports
  "~~/src/HOL/IMP/AExp"
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 3.12:
*)

type_synonym reg = "nat"
type_synonym rstate = "reg \<Rightarrow> int"
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun comp0 :: "aexp \<Rightarrow> nat \<Rightarrow> instr0 list" where
"comp0 (N n) sp = [LDI0 n]"
| "comp0 (V v) sp = [LD0 v]"
| "comp0 (Plus e1 e2) sp = comp0 e1 sp @ [MV0 (Suc sp)] @ comp0 e2 (Suc sp) @ [ADD0 (Suc sp)]"

definition rupdate :: "rstate \<Rightarrow> reg \<Rightarrow> val \<Rightarrow> rstate" where
"rupdate f a v = (\<lambda>x. (if x = a then v else (f x)))"

(* execute single instruction *)
fun exec0single :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec0single (LDI0 n) s rs = rupdate rs 0 n"
  | "exec0single (LD0 v) s rs = rupdate rs 0 (s v)" 
  | "exec0single (MV0 r) s rs = rupdate rs r (rs 0)"
  | "exec0single (ADD0 r) s rs = rupdate rs 0 ((rs 0) + (rs r))"

(* execute sequence of instrctions *)
fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec0 [] _ rs = rs"
  | "exec0 (i#is) s rs = exec0 is s (exec0single i s rs)" 

lemma rupdate_eq[simp]: "(rupdate rs r v) r = v" 
  apply(auto simp add: rupdate_def)
done

lemma rupdate_ne[simp]: "\<lbrakk>x \<noteq> y\<rbrakk> \<Longrightarrow> (rupdate rs x a) y = rs y"
apply (auto simp add: rupdate_def)
done

lemma exec_seq : "exec0 (xs@ys) s rs = exec0 ys s (exec0 xs s rs)" 
  apply(induction xs arbitrary: ys s rs)
  apply(auto)
done

(* Making sure generated code modifies only registers above SP, excep 0 *)

lemma reg_safe: "\<lbrakk>r \<noteq> 0 \<and> sp \<ge> r\<rbrakk> \<Longrightarrow> (exec0 (comp0 e sp) s rs) r = rs r"
  apply (induction e arbitrary: rs r sp)
  apply (auto simp add: exec_seq)
done

(* Prove that compiler is correct: for arbitrary expression 'a' it retuns evaluation results in register 0 *)

theorem "(exec0 (comp0 a sp) s rs) 0 = aval a s"
  apply (induction a arbitrary: sp s rs)
  apply(auto simp add: exec_seq reg_safe)
done


end

