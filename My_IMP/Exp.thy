theory Exp
  imports Main
begin
section \<open>Aexp\<close>
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V v) s = s v" |
"aval (Plus e1 e2) s = aval e1 s + aval e2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 0)"
value "aval (Plus (V ''x'') (V ''y'')) ((\<lambda>u. 0) (''x'' := 7, ''y'' := 3))"

text \<open>A little syntax magic to write larger states compactly:\<close>

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2 :: int))"
  by auto
 
value "aval (Plus (V ''x'') (V ''y'')) ((<> (''x'' := 7)) (''y'' := 3))"
value "aval (Plus (V ''x'') (V ''y'')) <''x'' := 7, ''y'' := 3>"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V v) = V v" |
"asimp_const (Plus e1 e2) = 
  (case (asimp_const e1, asimp_const e2) of
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
    (x1, x2)     \<Rightarrow> Plus x1 x2)"

lemma "aval (asimp_const a) s = aval a s"
  apply(induct a)
  by (auto split: aexp.split)

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N n1) (N n2) = N (n1 + n2)" |
"plus (N n1) e = (if n1=0 then e else Plus (N n1) e)" |
"plus e (N n2) = (if n2=0 then e else Plus e (N n2))" |
"plus e1 e2 = Plus e1 e2"

lemma aval_plus: 
  "aval (plus e1 e2) s = aval e1 s + aval e2 s"
  apply(induction e1 e2 rule: plus.induct)
  by simp_all

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V v) = V v" |
"asimp (Plus e1 e2) = plus (asimp e1) (asimp e2)"

lemma aval_simp[simp]:
  "aval (asimp a) s = aval a s"
  apply (induct a)
  apply simp_all
  by (simp add: aval_plus)

section \<open>Bexp\<close>
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc c) s = c" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

text \<open>some test of bexp\<close>
value "bval (Bc True) (\<lambda>x. 0)"
value "bval (Not (Bc True)) (\<lambda>x. 0)"
value "bval (And (Bc True) (Bc False)) (\<lambda>x. 0)"
value "bval (And (Bc True) (Bc True)) (\<lambda>x. 0)"
value "bval (Less (N 1) (N 0)) (\<lambda>x. 0)"
value "bval (Less (N 0) (N 1)) (\<lambda>x. 0)"

subsection \<open>Constant Folding\<close>
fun "not" :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

lemma bval_not[simp]:
  "bval (not b) s = (\<not> (bval b s))"
  apply (induct b)
  by auto

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"

lemma bval_and[simp]:
  "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
  apply (induction b1 b2 rule: and.induct)
  by auto

fun "or" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"or (Bc True) b = Bc True" |
"or b (Bc True) = Bc True" |
"or (Bc False) b = b" |
"or b (Bc False) = b" |
"or b1 b2 = not (and (not b1) (not b2))"

lemma bval_or:
  "bval (or b1 b2) s = (bval b1 s \<or> bval b2 s)"
  apply (induction b1 b2 rule: or.induct)
  by auto

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less a1 a2 = Less a1 a2"

lemma bval_less[simp]:
  "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
  apply (induction a1 a2 rule: less.induct)
  by auto

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc c) = Bc c" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

lemma bsimp_eq:
  "bval (bsimp b) s = bval b s"
  apply (induct b rule: bsimp.induct)
  by simp_all


end