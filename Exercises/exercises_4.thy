theory exercises_4
  imports Main
begin
text \<open>Exercise 4.1\<close>
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun "set" :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l a r) = (set l) \<union> {a} \<union> (set r)"

definition "test_tree1 = Node (Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip)) (4::int) (Node Tip 5 Tip)"
fun inord :: "int tree \<Rightarrow> int list" where
"inord Tip = []" |
"inord (Node l a r) = (inord l) @ [a] @ (inord r)"
(*
fun inc :: "int list \<Rightarrow> bool" where
"inc [] = True" |
"inc [x] = True" |
"inc (x#xs) = (if x>(hd xs) then False else (inc xs))"

value "inc [(2::int), 3, 5]"
*)
fun ord :: "int tree \<Rightarrow> bool" where
"ord t = strict_sorted (inord t)"

value "ord test_tree1"

fun rightest :: "int tree \<Rightarrow> int" where
"rightest (Node _ a Tip) = a" |
"rightest (Node _ a r) = rightest r"

fun leftest :: "int tree \<Rightarrow> int" where
"leftest (Node Tip a _) = a" |
"leftest (Node l a _) = leftest l"

fun ord1 :: "int tree \<Rightarrow> bool" where
"ord1 Tip = True" |
"ord1 (Node Tip a Tip) = True" |
"ord1 (Node Tip a r) = ((ord1 r) \<and> (a < leftest r))" |
"ord1 (Node l a Tip) = ((ord1 l) \<and> (rightest l < a))" |
"ord1 (Node l a r) = ((ord1 l) \<and> (ord1 r) \<and> (rightest l < a) \<and> (a < leftest r))"

value "ord1 test_tree1"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l a r) = (if x=a 
                        then (Node l a r) 
                        else if x < a 
                              then Node (ins x l) a r 
                              else Node l a (ins x r))"

value "ins 6 test_tree1"

lemma correctness_ins:
  "set (ins x t) = {x} \<union> set t"
  apply (induction t)
  by auto

lemma "ord1 t \<Longrightarrow> ord1 (ins i t)"
  apply (induction t arbitrary: i)
   apply auto
  sorry

text \<open>Exercise 4.2\<close>
inductive palindromes :: "'a list \<Rightarrow> bool" where
pal0: "palindromes []" |
palN: "palindromes xs \<Longrightarrow> palindromes (x # xs @ [x])"

lemma c_rev:
  "palindromes xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindromes.induct)
  by auto

text \<open>Exercise 4.3\<close>
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma aux0:
  "r x y \<Longrightarrow> star' r x y"
  by (metis refl' step')

lemma aux1:
  "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
   apply (simp add: aux0)
  by (rule step')

lemma eq_star1:
  "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (rule refl')
  by (simp add: aux1)

lemma aux3:
  "r x y \<Longrightarrow> star r x y"
  by (simp add: refl step)

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply (assumption)
  by (simp add: step)

lemma eq_star2:
  "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
   apply (rule refl)
  by (simp add: aux3 star_trans) 

text \<open>Exercise 4.4\<close>
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
it_refl: "iter r n x x" |
it_step: "r x0 x1 \<Longrightarrow> iter r n x1 xn  \<Longrightarrow> iter r (n+1) x0 xn"

lemma star_iter:
  "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply (induction rule: star.induct)
   apply (metis it_refl)
  by (metis it_step)

text \<open>Exercise 4.5\<close>
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
s_empty: "S []" |
s_1: "S s \<Longrightarrow> S (a # s @ [b])" |
s_2: "S s1 \<Longrightarrow> S s2 \<Longrightarrow> S (s1 @ s2)"

inductive T :: "alpha list => bool" where
t_empty: "T []" |
t_1: "T s1 \<Longrightarrow> T s2 \<Longrightarrow> T (s1 @ [a] @ s2 @ [b])"

lemma t_s:
  "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
   apply (metis s_empty)
  by (simp add: s_1 s_2)

lemma balance_composite_first:
  "T (w1 @ w2) ==> T w3 ==>  T (w1 @ w2 @ [a] @ w3 @ [b])"
  apply (simp)
  apply (rule t_1[of "w1 @ w2" w3, simplified])
  by (auto)

lemma com_t:
  "T s2 \<Longrightarrow> T s1 \<Longrightarrow> T (s1 @ s2)"
  apply (induction arbitrary: s1 rule: T.induct)
   apply (simp)
  using balance_composite_first by auto

lemma s_t:
  "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
    apply (rule t_empty)
  using t_empty t_1 apply fastforce
  by (simp add: com_t)

end
