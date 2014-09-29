theory Excercise52
  imports Main
begin

(*
By: Vadim Zaliva <vzaliva@cmu.edu>
From: T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL. Springer, 2014.
Exercise 5.2:
*)

lemma  "
  (\<exists> ys zs . xs=ys@zs \<and> length ys = length zs) \<or>
  (\<exists> ys zs . xs=ys@zs \<and> length ys = length zs +1)" (is "?C1 \<or> ?C2")
proof -
  {
    fix n assume A1: "length xs=n+n"
    hence ?C1 proof -
      obtain ys zs where "ys = take n xs \<and> zs = drop n xs" by blast
      hence "xs=ys@zs \<and> length ys = length zs" by (metis A1 add_diff_cancel_right' append_take_drop_id length_append length_drop length_splice)
      thus ?thesis by blast
    qed
  }
  note g1 = this

  {
    fix n assume A2:"length xs=(Suc n)+n"
    hence ?C2 proof -
      obtain ys zs where "ys = take (Suc n) xs \<and> zs = drop (Suc n) xs" by blast
      hence "xs=ys@zs \<and> length ys = length zs+1" by (metis A2 Suc_eq_plus1 add_diff_cancel_right' append_take_drop_id length_append length_drop nat_add_commute)
      thus ?thesis by blast
    qed
  }
  note g2 = this

  have "\<exists> b . (length xs=(b+b)) \<or> (length xs=((Suc b)+b))" by presburger
  then obtain b where "(length xs=(b+b)) \<or> (length xs=((Suc b)+b))" by blast
  from this g1 g2 show ?thesis by auto
qed

end
