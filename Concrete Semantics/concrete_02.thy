theory concrete_02
imports Main

begin
(*Type: bool*)
datatype bool = True | False

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

(*ºÃµÄ*)
(*Type: nat*)
datatype nat = 0 | Suc nat

(*define you own add*)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02: "add m 0 = m"
  apply(induction m)
   apply(auto)
  done

thm add_02

(*Type: list*)

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

declare [[names_short]]
value "rev(Cons True (Cons False Nil))"
value "rev(Cons (1::int) (Cons 2 Nil))"

(*prove: rev(rev a) = a*)

lemma app_assoc[simp]:
  "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  by auto

lemma app_Nil[simp]:
  "xs = app xs Nil"
  apply (induction xs)
  by auto

lemma rev_app[simp]:
  "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  by auto

theorem rev_rev[simp]: "rev(rev xs) = xs"
  apply(induction xs)
  apply auto
  done

(*2.2.5 Predefined Lists*)

(*2.3 Type and Function Definitions*)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror(mirror t) = t"
  apply(induction t)
   apply(auto)
  done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"
value "sq a"

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"
value "sq' a"


fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"


value "div2 6"

lemma "div2(n) = n div 2"
(*apply(induction n)*)
  apply(induction n rule: div2.induct)
    apply(auto)
  done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

(*
lemma "itrev xs [] = rev xs"
  apply(induction xs)
   apply(auto)
*)

(*it failed because rev has been overload above*)
lemma "itrev xs ys = rev xs @ ys"
  apply(induction xs arbitrary: ys)
   apply(auto)

end