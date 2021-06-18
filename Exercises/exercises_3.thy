theory exercises_3 
  imports Main "../My_IMP/Exp"
begin
text \<open>Exercise 3.1\<close>

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V v) = True" |
"optimal (Plus (N n1) (N n2)) = False" |
"optimal (Plus e1 e2) = ((optimal e1) \<and> (optimal e2))"

lemma "optimal (asimp_const e)"
  apply(induct e)
  by(auto split: aexp.split)

text \<open>Exercise 3.2\<close>
fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = (N n)" |
"full_asimp (V v) = (V v)" |
"full_asimp (Plus e1 e2) = 
  (case (full_asimp e1, full_asimp e2) of
    (N n1, N n2) \<Rightarrow> (N (n1 + n2)) |
    (N n1, (Plus e1' (N n2))) \<Rightarrow> (Plus e1' (N (n1 + n2))) |
    (N n1, (Plus (N n2) e2')) \<Rightarrow> (Plus (N (n1 + n2)) e2') |
    ((Plus e1' (N n1)), N n2) \<Rightarrow> (Plus e1' (N (n1 + n2))) |
    ((Plus (N n1) e2'), N n2) \<Rightarrow> (Plus (N (n1 + n2)) e2') |
    (a, b) \<Rightarrow> (Plus a b))"

lemma "aval (full_asimp a) s = aval a s"
  apply (induct a)
  by(auto split: aexp.split)

text \<open>Exercise 3.3\<close>
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = (N n)" |
"subst x a (V v) = (if v=x then a else (V v))" |
"subst x a (Plus e1 e2) = (Plus (subst x a e1) (subst x a e2))"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')"

lemma "aval (subst x a e) s = aval e (s (x := aval a s))"
  apply(induct e)
  by simp_all

text \<open>Exercise 3.4\<close>
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V v) s = s v" |
"aval (Plus e1 e2) s = aval e1 s + aval e2 s" |
"aval (Times e1 e2) s = aval e1 s * aval e2 s"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N n1) (N n2) = N (n1 + n2)" |
"plus (N n1) e = (if n1=0 then e else Plus (N n1) e)" |
"plus e (N n2) = (if n2=0 then e else Plus e (N n2))" |
"plus e1 e2 = Plus e1 e2"

lemma aval_plus[simp]: 
  "aval (plus e1 e2) s = aval e1 s + aval e2 s"
  apply (induction e1 e2 rule: plus.induct)
  by simp_all

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N n1) (N n2) = N (n1 * n2)" |
"times (N n1) e = (if n1=0 
                   then (N 0) 
                   else if n1=1
                        then e 
                        else (Times (N n1) e))" |
"times e (N n2) = (if n2=0 
                   then (N 0) 
                   else if n2=1
                        then e
                        else (Times e (N n2)))" |
"times e1 e2 = (Times e1 e2)"

value "times (plus (N 0) (N 0)) (V ''x'')"

lemma aval_times[simp]:
  "aval (times e1 e2) s = aval e1 s * aval e2 s"
  apply (induction e1 e2 rule: times.induct)
  by simp_all

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V v) = V v" |
"asimp (Plus e1 e2) = plus (asimp e1) (asimp e2)" |
"asimp (Times e1 e2) = times (asimp e1) (asimp e2)"

value "asimp (Plus (N 1) (Times (Plus (N 0) (V ''y'')) (V ''x'')))"

lemma "aval (asimp a) s = aval a s"
  apply(induction a)
  by simp_all

text \<open>Exercise 3.5\<close>
datatype aexp2 = N int 
  | V vname 
  | Plus aexp2 aexp2 
  | Times aexp2 aexp2 
  | Div aexp2 aexp2
  | Self_inc vname

(*
definition get_val :: "(val \<times> state) option \<Rightarrow> val option" where
"get_val x = (if Option.is_none x then None else Some (fst (the x)))"
(* How to prove the correctness of  get_val?*)
*)

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N n) s = Some (n, s)" |
"aval2 (V v) s = Some (s v, s)" |
"aval2 (Self_inc v) s = Some (s v, (s (v := (s v + 1))))" |
"aval2 (Plus e1 e2) s = (case (aval2 e1 s, aval2 e2 s) of
                          (None, None) \<Rightarrow> None|
                          (None, e2') \<Rightarrow> None |
                          (e1', None) \<Rightarrow> None |
                          (e1', e2') \<Rightarrow> Some ((fst (the e1')) + (fst (the e2')), s))" |
"aval2 (Times e1 e2) s = (case (aval2 e1 s, aval2 e2 s) of
                          (None, None) \<Rightarrow> None|
                          (None, e2') \<Rightarrow> None |
                          (e1', None) \<Rightarrow> None |
                          (e1', e2') \<Rightarrow> Some (fst (the e1') * fst (the e2'), s))" |
"aval2 (Div e1 e2) s = (case (aval2 e1 s, aval2 e2 s) of
                          (None, None) \<Rightarrow> None|                          
                          (None, e2') \<Rightarrow> None |
                          (e1', None) \<Rightarrow> None |
                          (e1', e2') \<Rightarrow> (if fst (the e2') = 0 then None else Some (fst (the e1') div fst (the e2'), s)))"


value "fst (the (Some (1::int, 2::int)))"
value "((4::int) div 2)"

value "aval2 (N 1) (\<lambda>x. 0)"
value "aval2 (V ''x'') (\<lambda>x. 0)"
value "aval2 (V ''x'') (snd (the (aval2 (Self_inc ''x'') (\<lambda>x. 1))))"
value "aval2 (Plus (N 1) (N 2)) (\<lambda>x. 0)"
value "aval2 (Plus (V ''x'') (N 1)) (\<lambda>x. 0)"
definition "now_x_state = snd (the (aval2 (Plus (Self_inc ''x'') (Plus (Self_inc ''x'') (N 0))) (\<lambda>x. 0)))"

text \<open>There is a problem: how maintain the state after self_inc\<close>
value "aval2 (Plus (Self_inc ''x'') (N 0)) (\<lambda>x. 0)"

text \<open>Exercise 3.6\<close>
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | Let vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
"lval (Nl n) s = n" |
"lval (Vl v) s = (s v)" |
"lval (Plusl e1 e2) s = (lval e1 s) + (lval e2 s)" |
"lval (Let v e1 e2) s = (lval e2 (s (v := lval e1 s)))"

value "lval (Let ''x'' (Plusl (Nl 1) (Nl 2)) (Plusl (Vl ''x'') (Vl ''x''))) (\<lambda>x. 0)"

fun inline :: "lexp \<Rightarrow> Exp.aexp" where 
"inline (Nl n) = (Exp.aexp.N n)" |
"inline (Vl v) = (Exp.aexp.V v)" |
"inline (Plusl e1 e2) = (Exp.aexp.Plus (inline e1) (inline e2))" |
"inline (Let v e1 e2) = (subst v (inline e1) (inline e2))"

lemma "Exp.aval (inline e) s = lval e s"
apply(induction e arbitrary: s)
     apply(auto split: lexp.split)
  sorry

text \<open>Exercise 3.7\<close>
fun eq :: "Exp.aexp \<Rightarrow> Exp.aexp \<Rightarrow> bexp" where
"eq a1 a2 = and (not (less a1 a2)) (not (less a2 a1))"

lemma correctness_eq[simp]:
  "bval (eq a1 a2) s = ((Exp.aval a1 s) = (Exp.aval a2 s))"
  by auto

fun le :: "Exp.aexp \<Rightarrow> Exp.aexp \<Rightarrow> bexp" where
"le a1 a2 = not (less a2 a1)"

lemma correctness_le[simp]:
  "bval (le a1 a2) s = ((Exp.aval a1 s) \<le> (Exp.aval a2 s))"
  by auto
 
text \<open>Exercise 3.8\<close>
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 Exp.aexp Exp.aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 c) s = c" |
"ifval (If i1 i2 i3) s = (if (ifval i1 s) then (ifval i2 s) else (ifval i3 s))" |
"ifval (Less2 a1 a2) s = ((Exp.aval a1 s) < (Exp.aval a2 s))"

value "ifval (Bc2 True) (\<lambda>x. 0)"
value "ifval (If (Bc2 True) (Bc2 False) (Bc2 True)) (\<lambda>x. 0)"
value "ifval (If (Bc2 False) (Bc2 False) (Bc2 True)) (\<lambda>x. 0)"
value "ifval (Less2 (Exp.N 1) (Exp.N 0)) (\<lambda>x. 0)"
value "Bc2 True = Bc2 False"

fun b_ifexp :: "bexp \<Rightarrow> ifexp" where
"b_ifexp (Bc c) = Bc2 c" |
"b_ifexp (Not b) = (If (b_ifexp b) (Bc2 False) (Bc2 True))" |
"b_ifexp (And b1 b2) = (If (b_ifexp b1) (b_ifexp b2) (Bc2 False))" |
"b_ifexp (Less a1 a2) = (Less2 a1 a2)"

lemma corectness_b_ifexp[simp]:
  "ifval (b_ifexp b) s = bval b s"
  apply (induct b)
  by auto

fun ifexp_bexp :: "ifexp \<Rightarrow> bexp" where
"ifexp_bexp (Bc2 c) = (Bc c)" |
"ifexp_bexp (If i1 i2 i3) = (or (And (ifexp_bexp i1) (ifexp_bexp i2)) (And (Not (ifexp_bexp i1)) (ifexp_bexp i3)))" |
"ifexp_bexp (Less2 a1 a2) = (Less a1 a2)"

lemma correctness_ifexp_bexp[simp]:
  "bval (ifexp_bexp ie) s = ifval ie s"
  apply (induct ie)
  by auto


text \<open>Exercise 3.9\<close>
type_synonym bval = bool
datatype pbexp = Pvar vname | Pnot pbexp | Pand pbexp pbexp | Por pbexp pbexp
type_synonym bstate = "vname \<Rightarrow> bval"

fun pbval :: "pbexp \<Rightarrow> bstate \<Rightarrow> bval" where
"pbval (Pvar v) s = s v" |
"pbval (Pnot b) s = (\<not> (pbval b s))" |
"pbval (Pand b1 b2) s = ((pbval b1 s) \<and> (pbval b2 s))" |
"pbval (Por b1 b2) s = ((pbval b1 s) \<or> (pbval b2 s))"

lemma "pbval (Pnot (Pand b1 b2)) s = pbval (Por (Pnot b1) (Pnot b2)) s"
  by auto

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (Pvar v) = True" |
(*
"is_nnf (Pnot b) = (case b of 
                      Pvar _ \<Rightarrow> True | 
                      _ \<Rightarrow> False)" |
*)
"is_nnf (Pnot (Pvar _)) = True" |
"is_nnf (Pnot _) = False" |
"is_nnf (Pand b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (Por b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

value "is_nnf (Pvar ''x'')"
value "is_nnf (Pnot (Pvar ''x''))"
value "is_nnf (Pnot (Pnot (Pvar ''x'')))"
value "is_nnf (Pand (Pnot (Pvar ''x'')) (Pnot (Pvar ''y'')))"
value "is_nnf (Pnot (Pand (Pnot (Pvar ''x'')) (Pnot (Pvar ''y''))))"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (Pvar v) = (Pvar v)" |
(* What's wrong?
"nnf (Pnot b) = (case b of
                  Pvar v \<Rightarrow> (Pnot (Pvar v)) |
                  Pnot b' \<Rightarrow> (nnf b') |
                  Pand b1 b2 \<Rightarrow> (Por (nnf (Pnot b1)) (nnf (Pnot b2))) |
                  Por b1 b2 \<Rightarrow> (Pand (nnf (Pnot b1)) (nnf (Pnot b2))))" |
*)
"nnf (Pnot (Pvar v)) = (Pnot (Pvar v))" |
"nnf (Pnot (Pnot b)) = nnf b" |
"nnf (Pnot (Pand b1 b2)) = (Por (nnf (Pnot b1)) (nnf (Pnot b2)))" |
"nnf (Pnot (Por b1 b2)) = (Pand (nnf (Pnot b1)) (nnf (Pnot b2)))" |
"nnf (Pand b1 b2) = (Pand (nnf b1) (nnf b2))" |
"nnf (Por b1 b2) = (Por (nnf b1) (nnf b2))"

value "nnf (Pvar ''x'')"
value "nnf (Pnot (Pnot (Pnot (Pvar ''x''))))"
value "nnf (Pnot (Pand (Pnot (Pnot (Pvar ''x''))) (Pnot (Pvar ''y''))))"
value "is_nnf (nnf (Pvar ''x''))"
value "is_nnf(nnf (Pnot (Pand (Pnot (Pvar ''x'')) (Pnot (Pvar ''y'')))))"
value "is_nnf(nnf (Pand (Pnot (Pnot (Pvar ''x''))) (Pvar ''y'')))"

lemma pbval_nnf[simp]:
  "pbval (nnf b) s = pbval b s"
  apply(induction b rule: nnf.induct)
  by auto
 
lemma correctness_nnf[simp]:
  "is_nnf (nnf pb)"
  apply (induction pb rule: nnf.induct)
  by auto

fun is_dnf_nnf :: "pbexp \<Rightarrow> bool" where
"is_dnf_nnf (Pvar v) = True" |
"is_dnf_nnf (Pnot b) = True" |
"is_dnf_nnf (Por b1 b2) = True" |
"is_dnf_nnf (Pand (Por b11 b12) b2) = False" |
"is_dnf_nnf (Pand b1 (Por b21 b22)) = False" |
"is_dnf_nnf (Pand b1 b2) = True"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf b =  (if is_nnf b 
              then is_dnf_nnf (nnf b) 
              else False)"

text \<open>assume it is a nnf\<close>
fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (Pvar v) = (Pvar v)" |
"dnf_of_nnf (Pnot b) = (Pnot b)" |
"dnf_of_nnf (Por b1 b2) = (Por (dnf_of_nnf b1) (dnf_of_nnf b2))" |
(*
"dnf_of_nnf (Pand b1 b2) = (case (dnf_of_nnf b1, dnf_of_nnf b2) of
                            ((Por b11 b12), b2') \<Rightarrow> (Por (Pand b11 b2) (Pand b12 b2)) |
                            (b1', (Por b21 b22)) \<Rightarrow> (Por (Pand b1' b21) (Pand b1' b22)))"
*)
"dnf_of_nnf (Pand (Por b11 b12) b2) = (Por (Pand (dnf_of_nnf b11) (dnf_of_nnf b2)) 
                                          (Pand (dnf_of_nnf b12) (dnf_of_nnf b2)))" |
"dnf_of_nnf (Pand b1 (Por b21 b22)) = (Por (Pand (dnf_of_nnf b1) (dnf_of_nnf b21))
                                          (Pand (dnf_of_nnf b1) (dnf_of_nnf b22)))" |
"dnf_of_nnf (Pand b1 b2) = (Pand b1 b2)"


lemma pbval_dnf_of_nnf[simp]:
  "pbval (dnf_of_nnf b) s = pbval b s"
  apply (induction b rule: dnf_of_nnf.induct)
  by auto

lemma correctness_convert[simp]:
  "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply (induction b rule: dnf_of_nnf.induct)
  apply (simp_all)
  using is_nnf.elims(2) apply fastforce
           apply meson
  apply metis
  apply presburger
        apply metis
  apply meson
  using is_nnf.elims(2) apply fastforce
  using is_nnf.elims(2) apply fastforce
  apply (metis is_dnf_nnf.simps(12) is_nnf.elims(2) nnf.simps(2) pbexp.distinct(1) pbexp.distinct(7) pbexp.distinct(9))
  using is_nnf.elims(2) apply fastforce
  using is_nnf.elims(2) by force



text \<open>Exercise 3.10\<close>
datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = (Some (n # stk))" |
"exec1 (LOAD x) s stk = (Some (s(x) # stk))" |
"exec1 ADD _ (j # i # stk) = (Some ((i + j) # stk))" |
"exec1 ADD _ _ = None "
(*
"exec1 ADD _ stk = (if length stk < 2 then None else (case stk of (j # i # xs) \<Rightarrow> (Some ((i+j) # xs))))"
*)

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i # is) s stk = (case (exec1 i s stk) of
                          None \<Rightarrow> None |
                          Some stk' \<Rightarrow> exec is s stk')"

fun comp :: "Exp.aexp \<Rightarrow> instr list" where
"comp (Exp.N n) = [LOADI n]" |
"comp (Exp.V x) = [LOAD x]" |
"comp (Exp.Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_append[simp]:
  "(exec is1 s stk = Some stk1) \<Longrightarrow> (exec (is1 @ is2) s stk) = (exec is2 s stk1)"
  apply(induction is1 arbitrary: stk)
   apply(simp_all)
  by (metis option.case_eq_if option.simps(3))

lemma correctness_asm[simp]:
  "exec (comp a) s stk = Some ((Exp.aval a s) # stk)"
  apply(induction a arbitrary: stk)
  by auto
  
text \<open>Exercise 3.11\<close>
type_synonym reg = nat
datatype instr_reg = LDI int reg | LD vname reg | ADD reg reg
type_synonym reg_state = "reg \<Rightarrow> int"

fun exec_reg1 :: "instr_reg \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec_reg1 (LDI n r) _ reg_s = reg_s (r := n)" |
"exec_reg1 (LD x r) s reg_s = reg_s (r := (s x))" |
"exec_reg1 (ADD r1 r2) _ reg_s = reg_s (r1 := (reg_s r1 + reg_s r2))"

fun exec_reg :: "instr_reg list \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec_reg [] _ reg_s = reg_s" |
"exec_reg (i # is) s reg_s = exec_reg is s (exec_reg1 i s reg_s)"

value "(exec_reg [(LDI 1 1), (LDI 2 2), (LDI 3 3), (ADD 2 3), (ADD 1 2)] (\<lambda>x. 0) (\<lambda>r. 0)) 1"

fun comp_reg :: "Exp.aexp \<Rightarrow> reg \<Rightarrow> instr_reg list" where
"comp_reg (Exp.N n) r = [LDI n r]" |
"comp_reg (Exp.V v) r = [LD v r]" |
"comp_reg (Exp.Plus e1 e2) r = (comp_reg e1 r) @ (comp_reg e2 (Suc r)) @ [ADD r (Suc r)]"

lemma l0[simp]:
  "exec_reg (i1 @ i2) s rs = exec_reg i2 s (exec_reg i1 s rs)"
  apply (induction i1 arbitrary: s rs)
  by simp_all

lemma left_alone[simp]:
  "r1 < r2 \<Longrightarrow> (exec_reg (comp_reg a r2) s rs) r1 = rs r1 "
  apply (induction a arbitrary: rs r2)
  by simp_all

lemma correctness_comp[simp]:
  "exec_reg (comp_reg a r) s rs r = Exp.aval a s"
  apply (induction a arbitrary: r rs)
  by simp_all  


text \<open>Exercise 3.12\<close>
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec01 (LDI0 n) s rs = rs (0 := n)" |
"exec01 (LD0 v) s rs = rs (0 := (s v))" |
"exec01 (MV0 r) s rs = rs (r := (rs 0))" |
"exec01 (ADD0 r) s rs = rs (0 := (rs r + rs 0))"

value "(exec01 (ADD0 1) <> <0 := 3, 1 := 2>) 0"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec0 [] _ rs = rs" |
"exec0 (i # is) s rs = exec0 is s (exec01 i s rs)"

lemma exec0_append[simp]:
  "exec0 (i1 @ i2) s rs = exec0 i2 s (exec0 i1 s rs)"
  apply (induction i1 arbitrary: s rs)
  by auto

fun comp0 :: "Exp.aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (Exp.N n) _ = [LDI0 n]" |
"comp0 (Exp.V v) _ = [LD0 v]" |
"comp0 (Exp.Plus a1 a2) r = (comp0 a2 (Suc r)) @ [MV0 (Suc r)] @ (comp0 a1 (Suc (Suc r))) @ [ADD0 (Suc r)]"
 
lemma left_alone2[simp]:
  "0 < r1 \<Longrightarrow> r1 < r2 \<Longrightarrow> exec0 (comp0 a r2) s rs r1 = rs r1"
  apply (induct a arbitrary: rs r2)
  by simp_all

lemma correctness_comp0[simp]:
  "exec0 (comp0 a r) s rs 0 = Exp.aval a s"
  apply (induction a arbitrary: r s rs)
  by simp_all

value "if (1::int)=2 then (3::int) else 4"
value "let x=1::int in (x + 1)"
datatype N = One | Suc N
fun case_test :: "N \<Rightarrow> bool" where
"case_test t = (case t of 
                  One \<Rightarrow> True | 
                  _ \<Rightarrow> False)"
value "case_test One"
value "case_test (Suc One)"
value "[(1::int)..6]"

end