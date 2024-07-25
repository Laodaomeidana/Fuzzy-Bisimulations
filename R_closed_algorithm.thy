theory R_closed_algorithm
  imports Complex_Main Bis_R_closed Proof
begin

fun R_closed_algo::"R\<Rightarrow>R\<Rightarrow> NFTS \<Rightarrow>R" where
"R_closed_algo [] _ _  = []"|
"R_closed_algo ((s0,t0)#xs) r f = (if (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)).
                                   Distr_equal_check_dl r (get_distr f s0 a1) (get_distr f t0 a1) f) 
                                   then (s0,t0)#R_closed_algo xs r f
                                   else R_closed_algo xs r f)"
lemma R_closed_algo_subset:"set (R_closed_algo r1 r2 f) \<subseteq> set r1"
  apply (induct r1 r2 f rule:R_closed_algo.induct) by auto

function algo_induct ::"R\<Rightarrow>NFTS\<Rightarrow>R" where
"algo_induct [] _ = []"|
"algo_induct r1 f = (if(R_closed_algo r1 r1 f) = r1 then r1 else algo_induct (R_closed_algo r1 r1 f) f)"
  by pat_completeness auto

lemma length_algo:" length (R_closed_algo r1 r2 f) \<le> length r1"
  apply (induct r1 arbitrary: r2 f)
  apply auto
  by (simp add: le_Suc_eq)
lemma length_algo_uneq:"R_closed_algo r1 r2 f \<noteq> r1 \<Longrightarrow> length (R_closed_algo r1 r2 f) < length r1"
  apply (induct r1 arbitrary: r2 f)
  apply auto
  by (metis less_Suc_eq)
termination
  apply (relation "measure (\<lambda>(r1, f). length r1)")
  apply auto
  apply (subgoal_tac "length (R_closed_algo r1 r1 f) \<noteq> length r1")
  apply (simp add: length_algo order_neq_le_trans )
  using length_algo_uneq by force


lemma R_closed_algo_lemma:"(s,t)\<in>set (R_closed_algo r1 r2 f) \<Longrightarrow>
                     \<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1) f"
  apply (induct r1)
  apply auto
  by (smt (z3) Pair_inject set_ConsD) 

lemma R_closed_algo_rule:"r = R_closed_algo r1 r2 f \<Longrightarrow> (s,t)\<in>set r \<Longrightarrow>
                     \<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1) f"
  apply (subgoal_tac "(s,t)\<in>set (R_closed_algo r1 r2 f) \<Longrightarrow>
                     \<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1) f")
  apply (induct r1 r2 f rule: R_closed_algo.induct)
  apply simp 
  apply auto
  by (simp add: R_closed_algo_lemma)
 
lemma BIS_Distr_equal:"r2=r \<Longrightarrow> R_closed_algo r r2 f = r \<Longrightarrow> (s,t)\<in>set r \<Longrightarrow> f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f)\<Longrightarrow>
                         (\<forall>a1\<in>set(get_act (s,t) f (allact f)). RL_check_dl r2 (get_distr f s a1) (get_distr f t a1))" 
  apply(subgoal_tac "\<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1) f") defer
  apply (metis R_closed_algo_rule)
  by (simp add: Distr_equal_check_dl_RL_check_dl)

lemma R_closed_algo_cor:
 assumes "equiv (allstates f) (set r)"
          "(get_R_states_set r)= (get_NFTS_states_set f)"
          "r=r2"
  shows "f\<noteq>[] \<Longrightarrow> R_closed_algo r r2 f = r \<Longrightarrow> BIS_RL r r2 f"
  apply (subgoal_tac "\<forall>(s,t)\<in>set r. (\<forall>a1\<in>set(get_act (s,t) f (allact f)). 
                      RL_check_dl r2 (get_distr f s a1) (get_distr f t a1))") defer
  using BIS_Distr_equal assms(1) assms(2) assms(3) apply blast
  apply (induct r)
  apply auto
  using R_closed_RL R_closed_algo_rule 
  by (metis (no_types, lifting) list.inject list.set_intros(1)) 

theorem algorithm_cor:
  assumes "equiv (allstates f) (set r) "
          "(get_R_states_set r)= (get_NFTS_states_set f)"
        shows"f\<noteq>[] \<Longrightarrow> r=algo_induct r1 f \<Longrightarrow> BIS_RL r r f"
  using assms
  apply (induct r1 f rule:algo_induct.induct)
  apply simp
  by (metis R_closed_algo_cor algo_induct.simps(2))





(*
fun States_init::"NFTS \<Rightarrow> State list list"where
"States_init [] = [] "

fun Distr_div::"State list \<Rightarrow> Distr list list \<Rightarrow> Distr list list" where
"Distr_div sl [] = []"|
"Distr_div sl x#xs = " 

fun Distr_part::"State list list \<Rightarrow> Distr list list \<Rightarrow> Distr list list"where


(*error*)
inductive_set Distr_div::"State set \<Rightarrow> Distr set \<Rightarrow> Distr set set" 
  for S::"State set" and D::"Distr set" where
"d1\<in>D \<Longrightarrow> d2\<in>D \<Longrightarrow> get_values_set d1 S = get_values_set d2 S \<Longrightarrow> {d1,d2}\<in> (Distr_div S D)"


lemma Distr_div_cor:"DS = Distr_div S D \<Longrightarrow> \<forall>D1\<in>DS. \<forall>d1\<in>D1. \<forall>d2\<in>D1. get_values_set d1 S = get_values_set d2 S"
  using Distr_div.simps by fastforce

inductive_set Distr_part::"State set \<Rightarrow> Distr set set \<Rightarrow> Distr set set" 
  for S::"State set" and DS::"Distr set set" where
"d1\<in>DS \<Longrightarrow> (Distr_div S d1) = {d1} \<Longrightarrow> d1\<in>(Distr_part S DS)"|
"d1\<in>DS \<Longrightarrow> (Distr_div S d1) \<noteq> {d1} \<Longrightarrow>d2\<in>(Distr_div S d1) \<Longrightarrow> d2 \<in> (Distr_part S DS)"

lemma Distr_part_cor:"DS = Distr_part S D \<Longrightarrow> \<forall>D1\<in>DS. \<forall>d1\<in>D1. \<forall>d2\<in>D1. get_values_set d1 S = get_values_set d2 S"
  by (smt (verit) Distr_div.intros Distr_div_cor Distr_part.simps singletonD)
 


inductive_set State_div::"(Act \<times> Distr set) \<Rightarrow> State set \<Rightarrow> NFTS \<Rightarrow> State set set" 
  for D::"(Act \<times> Distr set)" and S::"State set" and f::"NFTS" where
"s\<in>S \<Longrightarrow> a = fst D \<Longrightarrow> \<exists>d\<in>(snd D). (s,a,d)\<in> (set f) \<Longrightarrow>  "

*)

end