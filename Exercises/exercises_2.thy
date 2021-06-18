theory exercises_2
  imports Main

begin

text \<open>Exercise 2.1\<close>
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"


text \<open>Exercise 2.2\<close>
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

theorem add_assoc[simp]: "add (add a b) c = add a (add b c)"
  apply(induction a)
   apply(auto)
  done

theorem add_b0[simp]: "b = add b 0"
  apply(induction b)
   apply(auto)
  done

theorem add_suc_commu[simp]: "add (Suc a) b = add a (Suc b)"
  apply(induction a)
   apply(auto)
  done

theorem add_suc[simp]: "Suc (add a b) = add a (Suc b)"
  apply(induction a)
   apply(auto)
  done

theorem add_commu[simp]: "add a b = add b a"
  apply(induction a)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double n = add n n"

theorem double[simp]: "double m = add m m"
  apply(induction m)
   apply(auto)
  done

text \<open>Exercise 2.3\<close>

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count y Nil = 0" |
"count y (x # xs) = (if x=y then Suc (count y xs) else count y xs)" 
(*
"count ys (Cons x xs) = (let tmp = count ys xs
                         in (if ys=x then Suc tmp else tmp))"
*)

value "count (1::int) [1, 2, 1, 3, 1, 5]"

theorem list_less[simp]: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

text \<open>Exercise 2.4\<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil ys = Cons ys Nil" |
"snoc (Cons x xs) ys = Cons x (snoc xs ys)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

theorem rev_snoc[simp]: "reverse (snoc xs ys) = ys # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

theorem reverse_2[simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done


text \<open>Exercise 2.5\<close>
fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = (sum n) + (Suc n)"

lemma sum_n[simp]: "sum n = (n * (n + 1)) div 2"
  apply(induction n)
   apply(auto)
  done

text \<open>Exercise 2.6\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = (contents l) @ (a # (contents r))"

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0" |
"treesum (Node l a r) = Suc((treesum l) + (treesum r))"

fun listsum :: "nat list \<Rightarrow> nat" where
"listsum Nil = 0" |
"listsum (x # xs) = Suc (listsum xs)"

lemma listsum_1[simp]: "Suc (listsum (x1) + listsum (x2)) = listsum (x1 @ x # x2)"
  apply(induction x1)
(*why choose x1*)
   apply(auto)
  done

theorem equal_treesum_listsum[simp]: "treesum t = listsum (contents t)"
  apply(induction t)
   apply(auto)
  done

text \<open>Exercise 2.7\<close>

(*I think it need Functional Programming, which i have not touch*)
datatype 'a tree2 = Leave 'a | Node "'a tree2" 'a "'a tree2"
fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Leave x) = (Leave x)" |
"mirror2 (Node l a r) = (Node (mirror2 r) a (mirror2 l))"

definition "test = (Node (Node (Leave 4) 2 (Leave 5)) (1::int) (Leave 3))"
value "mirror2 (Node (Leave (1::int)) 2 (Leave 3))"
value "mirror2 test"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leave x) = [x]" |
"pre_order (Node l a r) = a # pre_order l @ pre_order r"

value "pre_order test"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leave x) = [x]" |
"post_order (Node l a r) = post_order l @ post_order r @ [a]"

value "post_order test"

lemma pre_post_eq[simp]:
  "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t)
  by auto

text \<open>Exercise 2.8\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # xs) = x # [a] @ (intersperse a xs)"

value "intersperse (1::int) [2, 3]"
value "intersperse (1::int) [2, 2, 2, 2, 2]"

(*totaly guass -,-! *)
theorem "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs)
   by auto


text \<open>Exercise 2.9\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

value "itadd 4 2"

(*What is wrong? why the color of highligt is purple? \<longrightarrow> collision*)
theorem "itadd m n = m + n"
  apply(induction m arbitrary: n)
  by auto

text \<open>Exercise 2.10\<close>
(*There is some problem: what if one node only have left or right child?*)
datatype tree0 = Leave | Node tree0 tree0
definition "test_tree0_1 = (Node (Node Leave Leave) Leave)"
fun count_tree0 :: "tree0 \<Rightarrow> nat" where
"count_tree0 Leave = 1" | 
"count_tree0 (Node l r) = count_tree0 l + count_tree0 r + 1"
value "count_tree0 test_tree0_1"
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" | 
"explode (Suc n) t = explode n (Node t t)"
value "count_tree0 (Node Leave Leave)"
value "count_tree0 (explode (1::nat) (Node Leave Leave))"

lemma "count_tree0 (explode n t) = ((count_tree0 t) + 1) * (2^n) - 1"
  apply (induction n arbitrary: t)
  by (auto simp add: algebra_simps)

text \<open>Exercise 2.11\<close>
datatype exp = Var | Const int | Add exp exp | Mult exp exp
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const n) x = n" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] _ = 0" |
"evalp (x#xs) x' = x +  x' * (evalp xs x')"

value "evalp [1] 3"
value "evalp [0, 2] (-1)"
value "evalp [4, 2, -1, 3] 1"

fun add_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_list [] [] = []" |
"add_list [] ys = ys" |
"add_list xs [] = xs" |
"add_list (x#xs) (y#ys) = (x+y) # add_list xs ys"

value "add_list [1, 1] [0, 1, 1, 1]"

fun mult_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_list [] ys = []" |
"mult_list (x#xs) ys = add_list (map (\<lambda>x'. x' * x) ys) (0 # mult_list xs ys)"

value "mult_list [1, 1, 1] [1]"
value "mult_list [1, 1, 1] [1, 1]"
value "map (\<lambda>x. x * 3) [(1::int), 2, 3]"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs (Const n) = [n]" |
"coeffs Var = [0, 1]" |
"coeffs (Add e1 e2) = add_list (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = mult_list (coeffs e1) (coeffs e2)"

lemma correctness_add_list[simp]:
  "evalp (add_list e1 e2) x = evalp e1 x + evalp e2 x"
  apply (induction e1 rule: add_list.induct)
  by (auto simp add: algebra_simps)

lemma aux_mult:
  "evalp (map ((*) a) e2) x = a * evalp e2 x"
  apply (induction e2)
  by (auto simp add: algebra_simps)

lemma correctness_mult_list[simp]:
  "evalp (mult_list e1 e2) x = evalp e1 x * evalp e2 x"
  apply (induction e1)
   by (auto simp add: algebra_simps aux_mult) 

lemma correctness_coeffs:
  "evalp (coeffs e) x = eval e x"
  apply (induction e arbitrary: x)
  by (auto simp add: algebra_simps)

end
