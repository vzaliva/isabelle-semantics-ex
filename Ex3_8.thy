theory Ex3_8
imports
  "~~/src/HOL/IMP/BExp"
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 3.8:
*)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 v) s = v" 
  | "ifval (If cond_exp then_branch else_branch) s = ifval (if ifval cond_exp s then then_branch else else_branch) s"
  | "ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bc2 v" 
  | "b2ifexp (Less a1 a2) = Less2 a1 a2"
  | "b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" 
  | "b2ifexp (And b1 b2) = If (b2ifexp b1) (If (b2ifexp b2) (Bc2 True) (Bc2 False)) (Bc2 False)" 

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 v) = Bc v" 
  | "if2bexp (Less2 a1 a2) = Less a1 a2"
  | "if2bexp (If cond_exp then_branch else_branch) = 
  (Not 
  (And 
     (Not (And (if2bexp cond_exp) (if2bexp then_branch)))
     (Not (And (Not (if2bexp cond_exp)) (if2bexp else_branch)))
  ))"

theorem "bval exp s = ifval (b2ifexp exp) s"
  apply(induction exp)
  apply(auto)
done

theorem "ifval exp s = bval (if2bexp exp) s"
  apply(induction exp)
  apply(auto)
done

end


