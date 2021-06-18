theory concrete_03
  imports Main

begin

(*3.1 Arithmetic Expressions*)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

value "N 5"
value "V ''x''"
value "Plus (V ''x'') (V ''y'')"
value "Plus (N 2) (Plus (V ''z'') (N 3))"

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(*The \<lambda>x.0 here means a state: x \<Rightarrow> 0*)
value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0)"
(*the same: f(a := b) = (\<lambda>x. if x = a then b else f x)*)
value "aval (Plus (N 3)(V ''x'')) (f(''x'' := 0))"

(*x + y + z + w, let x = 7, y = 3, others = 0*)
value "aval (Plus (V ''x'') (Plus (V ''y'') (Plus (V ''z'') (V ''w'')))) (((\<lambda>x. 0)(''x'':=7))(''y'':=3))"
(*the same: error \<rightarrow> how to use <''x'':=7, ''y'':=3>*)
(*value "aval (Plus (V ''x'') (Plus (V ''y'') (Plus (V ''z'') (V ''w'')))) <''x'':=7, ''y'':=3>"*)

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) = 
  (case (asimp_const a1, asimp_const a2) of 
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
     (b1, b2) \<Rightarrow> Plus b1 b2
  )
"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
    (*Why the split is wrote with auto not above?*)
    (*\<rightarrow> The split modifier is the hint to auto to perform a case split whenever it sees a case expression over aexp.*)
    apply(auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i=0 then a else (Plus (N i) a))" |
"plus a (N i) = (if i=0 then a else (Plus a (N i)))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus[simp]: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
  apply(auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply(induction a)
    apply(auto)
(*it's so sad... I don't know where is wrong.*)
(*it's ok after rewriting the done of aval_plus...*)
  done

(*3.2 Boolean Expressions*)
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

(*The following is some optimizing versions of the constructors.*)
fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
(*why this and has parentheses? collision with the keyword and?*)
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"
(*Note that in the Less case we must switch from bsimp to asimp \<rightarrow> Why?*)

(*3.3 Stack Machine and Compilation*)
datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

abbreviation "hd2 xs \<equiv> hd (tl xs)"
abbreviation "tl2 xs \<equiv> tl (tl xs)"

(*It's tooooo hard for me now. Saaaaad... /TAT\*)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x) s stk = s(x) # stk" |
"exec1 ADD _ stk = (hd2 stk + hd stk) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i # is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma pre_exec_1: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply(induction is1)
  apply(auto)
(*where is wrong again?*)

lemma "exec (comp a) s stk = aval a s # stk"
  apply(induction a)
    apply(auto)



end