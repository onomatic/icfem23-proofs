theory Traces
imports Main
begin

find_consts "'a + 'b \<Rightarrow> bool"

term sum.isl 

definition "traceDom \<equiv> {(f). \<forall> (i :: nat) j. j \<le> i \<longrightarrow> \<not>(sum.isl (f j)) \<longrightarrow> f i = f j}"

typedef ('state, 'sym) trace = "traceDom :: (nat \<Rightarrow> ('state + 'sym)) set"
  apply (rule_tac x="\<lambda>_. Inr undefined" in exI)
  apply (clarsimp simp: traceDom_def)
  done

setup_lifting type_definition_trace     


lift_definition index :: " ('state, 'sym) trace \<Rightarrow> nat \<Rightarrow>  'state + 'sym" is "\<lambda>f n. f n" done

primrec iterate where
  "iterate x f 0       = x" |
  "iterate x f (Suc n) = f (iterate x f n)" 

definition "finiteS f \<equiv> \<exists>n. \<not>isl (index f n)"

lift_definition pred :: "((nat \<Rightarrow>  'state + 'sym) \<Rightarrow> 'b) \<Rightarrow> ( ('state, 'sym) trace \<Rightarrow> 'b)" is "\<lambda>P f. P f"
  done

definition lengthS where "lengthS \<equiv> \<lambda>f. if finiteS f then Some (LEAST n. \<not>isl (index f n)) else None"

lift_definition liftF :: "(nat \<Rightarrow>  'state + 'sym) \<Rightarrow>  ('state, 'sym) trace " is
 "\<lambda>f. if f \<in> traceDom then f else (\<lambda>_. Inr undefined)" 
  by (clarsimp simp: traceDom_def)

lemma traceDom_antimono: "g \<in> traceDom \<Longrightarrow> antimono P \<Longrightarrow> (\<And>n. P n \<longrightarrow> isl (f n)) \<Longrightarrow> (\<lambda>n. if P n then f n else g n ) \<in> traceDom"
  apply ( clarsimp simp: traceDom_def split: if_splits)
  by (metis monotoneD)

lemma traceDom_antimono': "\<not>(\<lambda>n. if P n then f n else g n ) \<in> traceDom \<Longrightarrow>  antimono P \<Longrightarrow> (\<And>n. P n \<Longrightarrow> isl (f n)) \<Longrightarrow> \<not>g \<in> traceDom "
  apply ( clarsimp simp: traceDom_def split: if_splits)
  by (metis monotoneD)

primrec coerce :: "'a + 'b \<Rightarrow> 'a + 'c"
  where
  "coerce (Inl a) = Inl a" |
  "coerce (Inr b) = Inr undefined"


definition "tail s = liftF (\<lambda>n. index s (n + 1))"

lemma tail_traceDom[simp]: "(\<lambda>n. index s (n + 1)) \<in> traceDom"
  by (clarsimp simp: traceDom_def, transfer, clarsimp simp: traceDom_def)


lemma lengthS_le: "(\<And>n.  isl (index s n) \<Longrightarrow> isl (index s' n)) ==>  finiteS s' \<Longrightarrow>   the ( lengthS s) \<le> the (lengthS s')"
  apply (transfer)
  apply (clarsimp simp: lengthS_def )
  apply (intro conjI impI; clarsimp?)
   apply (rule Least_le)
   apply (metis LeastI finiteS_def)
  by (simp add: finiteS_def)


definition "map_trace f t \<equiv> liftF (\<lambda>n. case_sum (Inl o f) (Inr) (index t n))"

lemma map_traceDom[simp]: "(\<lambda>n. case_sum (Inl o f o projl) (Inr) (index t n)) \<in> traceDom"
  apply (clarsimp simp: traceDom_def split: sum.splits)
  apply (intro conjI; clarsimp)
   apply (transfer, clarsimp simp: traceDom_def)
  apply (transfer, clarsimp simp: traceDom_def)
  done

lemma trace_eqI: "(\<And>n. index c n = index d n) \<Longrightarrow> c = d" sorry

definition appendS :: " ('state, 'sym) trace \<Rightarrow>  ('state, 'sym) trace \<Rightarrow>  ('state, 'sym) trace"
  where "appendS s s' \<equiv> 
   if finiteS s then
       liftF (\<lambda>n. if (n < the ( lengthS s)) then coerce (index s n) else index s' (n - (the (lengthS s))))
                        else
       liftF (coerce o index s)"

end