theory concrete_05
  imports Main
begin

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app [] ys = ys" |
"app (x # xs) ys = x # app xs ys"

thm app.simps
thm app.simps(1)
thm app.simps(1-2)

thm surj_def

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>y. \<exists>x. y = f x" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  from this show "False" by blast
qed

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof 
  assume 0: "surj f"
  have 1: "\<exists>a. {x. x \<notin> f x} = f a" using 0 by (auto simp: surj_def)
  show "False" using 1 by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists>a. {x. x \<notin> f x} = f a" using s
    by (auto simp: surj_def) 
  thus "False" by blast
qed

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

lemma fixes a b :: int assumes "b dvd (a + b)" shows "b dvd a"
proof -
  have "\<exists>k'. a = b * k'" if asm: "a + b = b * k" for k
  proof
    show "a = b * (k - 1)" using asm by (simp add: algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

end