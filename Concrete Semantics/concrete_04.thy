theory concrete_04
  imports Main

begin
(*4.1 Formulas*)
(*form ::=(form) | True | Flase | term = term |
  \<not> form | form \<and> form | form \<or> form |
  form \<longrightarrow> form | \<forall>x.form | \<exists>x.form*)
(*4.2 Sets*)

(*4.3 Proof Automation*)
lemma "\<forall>x. \<exists>y. x=y" 
  apply(auto)
  done

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma "\<lbrakk>\<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A\<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n"
  (*apply(auto)*)
  by fastforce

lemma 
  "\<lbrakk>\<forall>x y. T x y \<or> T y x;
    \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
    \<forall>x y. T x y \<longrightarrow> A x y\<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
  by blast

(*4.3.1 Sledgehammer*)
lemma "\<lbrakk>xs @ ys = ys @ xs; length xs = length ys\<rbrakk> \<Longrightarrow> xs = ys"
  (*sledgehammer*)
  using append_eq_append_conv by blast

(*4.3.2 Arithmetic*)
lemma "\<lbrakk>(a::nat) \<le> x + b; 2*x < c\<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
  by arith

(*4.4 Single Step Proofs*)
(*conjI[of "a=b" "False"]*)

lemma "\<lbrakk>(a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e\<rbrakk> \<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]]

thm Suc_leD
lemma "Suc (Suc (Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by(blast dest:Suc_leD)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" | 
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

(*Prove ev 4*)
(*Doesnt work?\<rightarrow>evSS[OF evSS[OF ev0]]*)
lemma "ev (Suc (Suc (Suc (Suc 0))))"
  apply(rule evSS)
  apply(rule evSS)
  apply(rule ev0)
  done

(*Prove the above is equivalent*)
lemma "ev m \<Longrightarrow> evn m"
  apply(induction rule: ev.induct)
  by(simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
  by(simp_all add: ev0 evSS)

declare ev.intros[simp, intro]

(*4.5.2 The Reflexive Transitive Closure*)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z" 

thm refl
thm step
lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(assumption)
  apply(metis step)
  done

end