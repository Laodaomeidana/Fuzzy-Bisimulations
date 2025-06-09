theory Proof
  imports Bisimulation Bis_R_closed 
begin

lemma partition_init_subset_nonempty:
  "f\<noteq>[] \<Longrightarrow>s = (partition_init r (get_NFTS_states_set f)) \<Longrightarrow> \<forall>(s0,t0)\<in>set r. (subset s0 s)\<noteq>{}\<and>(subset t0 s)\<noteq>{}"
using partition_init_def get_R_states_set_notempt subset_union by auto

lemma Rright_R_closed_set:"\<forall>(s0,t0)\<in>set r. (subset s0 s)\<noteq>{}\<and>(subset t0 s)\<noteq>{} \<Longrightarrow> B\<in>partition r s 
                            \<Longrightarrow>(s1,t1)\<in>set r \<Longrightarrow> s1\<in>B \<Longrightarrow> set (R_right r s1) \<subseteq> B"
  by (smt (verit) R_right_correct case_prod_conv partition_correct_s0t0 subsetI)

lemma Rright_R_closed_set_2:"f\<noteq>[] \<Longrightarrow>s = (partition_init r (get_NFTS_states_set f)) \<Longrightarrow> B\<in>partition r s 
                            \<Longrightarrow>(s1,t1)\<in>set r \<Longrightarrow> s1\<in>B \<Longrightarrow> set (R_right r s1) \<subseteq> B"
  apply (subgoal_tac"t1 \<in> set (R_right r s1) \<and> t1\<in>B") defer
  using R_right_correct partition_correct partition_init_subset_nonempty
  apply (smt (verit) old.prod.case surj_pair)
  apply auto
  apply (subgoal_tac "(s1,x)\<in> set r") defer
  using R_right_subset apply blast
  using partition_init_subset_nonempty by (smt (verit, best) Rright_R_closed_set in_mono)

lemma Rleft_R_closed_set:"\<forall>(s0,t0)\<in>set r. (subset s0 s)\<noteq>{}\<and>(subset t0 s)\<noteq>{} \<Longrightarrow> B\<in>partition r s 
                            \<Longrightarrow>(s1,t1)\<in>set r \<Longrightarrow> t1\<in>B \<Longrightarrow> set (R_left r t1) \<subseteq> B"
  by (smt (verit, del_insts) R_left_correct case_prodD partition_correct subsetI)

lemma Rleft_R_closed_set_2:"f\<noteq>[] \<Longrightarrow>s = (partition_init r (get_NFTS_states_set f)) \<Longrightarrow> B\<in>partition r s 
                            \<Longrightarrow>(s1,t1)\<in>set r \<Longrightarrow> t1\<in>B \<Longrightarrow> set (R_left r t1) \<subseteq> B"
  apply (subgoal_tac"s1 \<in> set (R_left r t1) \<and> s1\<in>B") defer
  using  R_left_correct partition_correct partition_init_subset_nonempty
  apply fastforce
  apply auto
  apply (subgoal_tac "(x,t1)\<in> set r") defer
  using R_left_subset apply blast
  using partition_init_subset_nonempty 
  by (smt (verit) Rleft_R_closed_set in_mono)

lemma R_closed_set_allstate_inR:
  "f\<noteq>[] \<Longrightarrow>(get_R_states_set r) = (get_NFTS_states_set f)\<Longrightarrow>B\<in>(R_closed_set r f)\<Longrightarrow> \<forall>s\<in>B. s\<in>set (get_R_states r)"
  by (simp add: R_closed_set_def get_R_states_list_set_elem partition_get_R_states_set partition_init_correct)

lemma allstate_inR_closed_set:
  "f\<noteq>[] \<Longrightarrow>(get_R_states_set r) = (get_NFTS_states_set f)\<Longrightarrow>(\<forall>s1\<in>set(get_R_states r). \<exists>B\<in>(R_closed_set r f). s1\<in>B)"
  by (metis R_closed_set_def UnionE get_R_states_set_list partition_init_correct partition_invariance union_set_def)
 
lemma get_Distr_states_set_get_states:"\<Union>(get_Distr_states_set u) = set (get_states u)"
  by (induct u) auto

lemma get_NFTS_states_set_allstates:"\<Union>(get_NFTS_states_set f) = (allstates f)"
  apply (induct f) apply simp
  apply (subgoal_tac "(get_NFTS_states_set (a # f)) = {{fst a}} \<union> (get_Distr_states_set (snd (snd a))) \<union> get_NFTS_states_set f") defer
  apply simp
  apply (subgoal_tac "allstates (a # f) = {fst a} \<union> set (get_states (snd (snd a))) \<union> allstates f") defer
  apply simp
  apply (subgoal_tac "\<Union>(get_Distr_states_set (snd (snd a))) = set (get_states (snd (snd a)))")
  apply simp
  by (simp add: get_Distr_states_set_get_states)


lemma partition_init_finite:"f\<noteq>[] \<Longrightarrow>finite (\<Union>(partition_init r (get_NFTS_states_set f)))"
  apply (auto simp add: partition_init_def) defer
  apply (metis List.finite_set get_R_states_set_list)
  apply (simp add: get_NFTS_states_set_notempty)
  apply (subgoal_tac "finite(\<Union>(get_NFTS_states_set f))")
  apply (metis partition_not_inR_subset1 rev_finite_subset union_set_def) 
  apply (induct f) apply auto          
  apply (simp_all add: get_Distr_states_set_get_states)
  apply fastforce apply fastforce by fastforce

lemma R_closed_set_finite:"f\<noteq>[] \<Longrightarrow>B\<in>(R_closed_set r f) \<Longrightarrow> finite B"
  apply (simp add:R_closed_set_def)
  apply (subgoal_tac "B \<subseteq> \<Union>(partition_init r (get_NFTS_states_set f))") defer
  using partition_subset union_set_def apply blast
  apply (subgoal_tac "finite (\<Union>(partition_init r (get_NFTS_states_set f)))")
  apply (simp add: rev_finite_subset)
  by (simp add: partition_init_finite)


lemma partition_allR:"s = (get_R_states_set r)\<Longrightarrow> B \<in> partition r s \<Longrightarrow> (s0,t0) \<in> set r \<Longrightarrow> s0 \<in> B \<longleftrightarrow> t0 \<in> B"
  apply (subgoal_tac "(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}") defer
  apply (simp add: get_R_states_set_notempt)
  by (simp add: partition_correct)
lemma partition_inR_notequivR:"s=(get_R_states_set r) \<Longrightarrow> B \<in> partition r s \<Longrightarrow>s1\<in>B \<Longrightarrow> \<exists>t1\<in>B. ((s1,t1)\<in>set r) \<or> ((t1,s1)\<in>set r)"
  apply (subgoal_tac "B \<subseteq> \<Union>(get_R_states_set r)") defer
  using partition_subset union_set_def apply auto[1]
  apply (subgoal_tac "\<forall>(s0,t0)\<in>set r . (s0\<in>B) = (t0\<in>B)") defer
  using partition_allR apply blast 
  by (smt (verit) Un_iff case_prodD get_R_states_set get_R_states_set_list mem_Collect_eq subset_iff)

lemma partition_inR_equivR_initS:"equiv (\<Union>(get_R_states_set r)) (set r) \<Longrightarrow> B\<in>(get_R_states_set r) \<Longrightarrow> s1\<in>B \<Longrightarrow>t1\<in>B\<Longrightarrow>(s1,t1)\<in>set r"
  apply (simp only: equiv_def)
  apply (case_tac r)
  apply auto
  using refl_onD apply fastforce
  using UnionI empty_iff get_R_states_set_subset insert_iff prod.inject refl_onD surj_pair apply fastforce
  apply (meson insert_iff old.prod.inject refl_onD)
  using get_R_states_set_subset insert_iff prod.inject refl_onD by fastforce


lemma partition_getsets_subset_uneq:"r= (x#xs)\<Longrightarrow>equiv (\<Union>(get_R_states_set r)) (set r) \<Longrightarrow> s=(get_R_states_set r) \<Longrightarrow> B \<in> ss \<Longrightarrow>
       ss =(s - subset (fst x) s -subset (snd x) s \<union> {union_set (subset (fst x) s) \<union> union_set (subset (snd x) s)}) 
       \<Longrightarrow> s1\<in>B \<Longrightarrow>t1\<in>B\<Longrightarrow>(s1,t1)\<in>set r"
  apply (subgoal_tac "\<forall>B\<in>s. \<forall>s1\<in>B. \<forall>t1\<in>B. (s1,t1)\<in>set r") defer
  using partition_inR_equivR_initS apply blast
  apply (simp only: equiv_def subset_def union_set_def)
  apply auto
  using get_R_states_set_subset apply blast
  apply (smt (verit) get_R_states_set_subset insert_compr mem_Collect_eq prod.collapse)
  apply (metis (no_types, opaque_lifting) get_R_states_set_subset insertE insertI1 prod.exhaust_sel subset_empty2 subset_empty_iff sym_def)
  using get_R_states_set_subset by blast

lemma partition_subset_uneq:"x\<in>r \<Longrightarrow> equiv (\<Union>s) r \<Longrightarrow> \<forall>B\<in>s. \<forall>s1\<in>B. \<forall>t1\<in>B. (s1,t1)\<in> r \<Longrightarrow>
      \<forall>B\<in>((s-(subset (fst x) s)-(subset (snd x) s)) \<union> ({union_set(subset (fst x) s) \<union> union_set(subset (snd x) s)})). \<forall>s1\<in>B. \<forall>t1\<in>B. (s1,t1)\<in>r"
  apply (simp only: equiv_def subset_def union_set_def)
  apply auto
  apply (meson transD)
  apply (smt (verit, del_insts) prod.exhaust_sel transD)
  apply (smt (verit) fst_conv prod.exhaust_sel snd_conv sym_def transD)
  by (meson transD)

lemma insert_union:"(insert (union_set (subset (fst a) s) \<union> union_set (subset (snd a) s))(s - subset (fst a) s - subset (snd a) s)) = 
       ((s-(subset (fst a) s)-(subset (snd a) s)) \<union> ({union_set(subset (fst a) s) \<union> union_set(subset (snd a) s)}))"
  by auto

lemma partition_inR_equivR:"\<forall>B\<in>s. \<forall>s1\<in>B. \<forall>t1\<in>B. (s1,t1)\<in>r1 \<Longrightarrow> set r \<subseteq> r1 \<Longrightarrow> equiv (\<Union>s) r1 \<Longrightarrow> \<forall>B\<in>partition r s. \<forall>s1\<in>B. \<forall>t1\<in>B. (s1,t1)\<in>r1"
  apply (induct r arbitrary:s)
  apply (metis Bis_R_closed.partition.simps(1))
  apply (subgoal_tac "partition (a # r) s = (if(subset (fst a) s = subset (snd a) s) then partition r s 
                     else partition r ((s-(subset (fst a) s)-(subset (snd a) s)) \<union> ({union_set(subset (fst a) s) \<union> union_set(subset (snd a) s)})))")
  apply (simp add:if_splits) defer
  using Bis_R_closed.partition.simps(2) apply presburger 
  apply (case_tac "Bis_R_closed.subset (fst a) s = Bis_R_closed.subset (snd a) s")
  apply simp_all 
  apply (subgoal_tac "\<forall>B\<in>(insert (union_set (subset (fst a) s) \<union> union_set (subset (snd a) s))
              (s - subset (fst a) s - subset (snd a) s)).
          \<forall>s1\<in>B. \<forall>t1\<in>B. (s1, t1) \<in> r1 ") defer
  using partition_subset_uneq insert_union apply presburger
  apply (subgoal_tac "set r \<subseteq> r1")defer
  apply blast
  apply (subgoal_tac "\<Union> s =\<Union> (insert (union_set (Bis_R_closed.subset (fst a) s) \<union> union_set (Bis_R_closed.subset (snd a) s))
              (s - Bis_R_closed.subset (fst a) s - Bis_R_closed.subset (snd a) s))") 
  apply (smt (verit))
  by (smt (verit, ccfv_SIG) Bis_R_closed.partition.simps(2) insert_union partition_invariance union_set_def)

lemma partition_correct_rtrancl_lemma:"\<forall>B\<in>s. \<forall>s2\<in>B. \<forall>t2\<in>B. (s2,t2)\<in>rtrancl(set r)\<or>(t2,s2)\<in>rtrancl(set r) \<Longrightarrow> x\<in> (set r) \<Longrightarrow>
       ss=(s - subset (fst x) s -subset (snd x) s \<union> {union_set (subset (fst x) s) \<union> union_set (subset (snd x) s)}) \<Longrightarrow> s=(get_R_states_set r) \<Longrightarrow>
       \<forall>B\<in>ss. \<forall>s2\<in>B. \<forall>t2\<in>B. (s2,t2)\<in>rtrancl(set r)\<or>(t2,s2)\<in>rtrancl(set r)"
  apply auto
  apply (meson get_R_states_set_fst_subset_in)
  apply (metis empty_iff get_R_states_set_fst_subset_in get_R_states_set_snd_subset_in get_R_states_set_subset prod.collapse r_into_rtrancl singletonD subset_correct2 union_set_empty2)
  apply (metis empty_iff get_R_states_set_fst_subset_in get_R_states_set_snd_subset_in get_R_states_set_subset prod.collapse r_into_rtrancl singletonD subset_correct2 union_set_empty2)
  by (metis get_R_states_set_snd_subset_in)


lemma partition_inR_lemma:"s=(get_R_states_set r) \<Longrightarrow> B \<in> partition r s \<Longrightarrow> equiv (\<Union>(get_R_states_set r)) (set r) \<Longrightarrow> 
                           s1\<in>B \<Longrightarrow>t1\<in>B\<Longrightarrow>(s1,t1)\<in>set r \<and> (t1,s1)\<in>set r"
  by (meson order_refl partition_inR_equivR_initS partition_inR_equivR)

lemma partition_inR:" f\<noteq>[] \<Longrightarrow>B \<in>partition r (partition_init r (get_NFTS_states_set f)) \<Longrightarrow>s1\<in>set(get_R_states r) 
                      \<Longrightarrow>(get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow> equiv (allstates f) (set r) 
                      \<Longrightarrow> s1\<in>B \<Longrightarrow>t1\<in>B\<Longrightarrow>  (s1,t1)\<in>set r \<and> (t1,s1)\<in> set r"
  apply (simp add: partition_init_def)
  apply (subgoal_tac "get_NFTS_states_set f \<noteq> {}") defer
  using partition_Sempty 
  apply simp apply (metis Un_insert_left get_NFTS_states_set.elims insert_not_empty)
  apply (subgoal_tac "\<Union>(get_NFTS_states_set f) = (allstates f)")
  using get_R_states_notempty partition_inR_lemma partition_init_correct partition_init_def apply fastforce
  by (simp add: get_NFTS_states_set_allstates) 
 
lemma R_closed_set_relation:
  " f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r) \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>
  s1\<in> set(get_R_states r) \<Longrightarrow> B\<in>(R_closed_set r f) \<Longrightarrow> s1\<in>B \<Longrightarrow> set (R_right r s1) = B \<and> set (R_left r s1) = B"
  apply (simp add: R_closed_set_def)
  apply (simp add: partition_init_def)
  apply (subgoal_tac "get_NFTS_states_set f \<noteq> {}") defer
  using partition_Sempty apply (metis Un_insert_left get_NFTS_states_set.elims insert_not_empty) 
  apply simp
  apply auto defer 
  apply (subgoal_tac "(s1,xa) \<in> set r")
  apply (simp add: R_right_correct)
  apply (metis empty_iff partition_inR partition_init_def) 
  apply (smt (verit, ccfv_SIG) Rleft_R_closed_set_2 empty_iff in_mono partition_inR partition_init_def)
  apply (metis R_left_correct empty_iff partition_inR partition_init_def)
  by (smt (verit, ccfv_SIG) Rright_R_closed_set_2 empty_iff in_mono partition_inR partition_init_def)



lemma get_values_range:"get_values \<mu> L\<ge>0"
  apply (induct \<mu> L rule:get_values.induct) by simp_all
lemma get_values_elims:"s1\<in>set L \<Longrightarrow> (get_value \<mu> s1) \<le> (get_values \<mu> L)"
  apply (induct \<mu> L rule: get_values.induct) by auto
lemma get_values_app:"get_values \<mu> (xs@ys) = max (get_values \<mu> xs) (get_values \<mu> ys)"
  apply (induct xs)
  apply simp
  apply auto
  apply (subgoal_tac "max (get_values \<mu> []) (get_values \<mu> ys) = max 0 (get_values \<mu> ys)")
  apply (simp add: get_values_range)
  apply (metis get_values.simps(1) get_values.simps(2) neq_Nil_conv)
  by (smt (verit) get_values.simps(1) get_values.simps(3) list.exhaust max.assoc max.commute max.idem)

lemma MAX_insert:
  assumes "finite b"
  shows " Max ({a} \<union> (insert 0 b)) = max a (Max (insert 0 b))"
proof (cases "b = {}")
  case True
  then show ?thesis
    by (metis Max.union Max_singleton finite.emptyI finite.insertI insert_not_empty) 
next
  case False
  then have "{a} \<union> (insert 0 b) = insert a (insert 0 b)" by auto
  then have "Max ({a} \<union> (insert 0 b)) = Max (insert a (insert 0 b))" by simp
  also have "... = max a (Max (insert 0 b))" 
    using Max.insert assms
    by (simp add: max.commute)
  finally show ?thesis by simp
qed

lemma get_values_set_eq_lemma:
  assumes "finite {y. \<exists>x\<in>set L. y = get_value \<mu> x}"
  shows "get_values \<mu> L = Max ({y. \<exists>x\<in>set L. y = get_value \<mu> x} \<union> {0})"
  apply (induct L)
  apply simp_all
  using get_values.elims apply blast 
  apply (subgoal_tac "get_values \<mu> (a # L) = max (get_value \<mu> a) (get_values \<mu> L)") defer 
  apply (smt (verit, best) get_values.elims get_values.simps(3) get_values_elims list.set_intros(1) max.commute max.order_iff)
  apply (subgoal_tac "Max (insert 0 {y. y = get_value \<mu> a \<or> (\<exists>x\<in>set L. y = get_value \<mu> x)})=
                     max (get_value \<mu> a) (Max (insert 0 {y. \<exists>x\<in>set L. y = get_value \<mu> x}))")
  apply presburger
  apply (subgoal_tac "{y. y = get_value \<mu> a \<or> (\<exists>x\<in>set L. y = get_value \<mu> x)} = 
                      {get_value \<mu> a} \<union> {y. \<exists>x\<in>set L. y = get_value \<mu> x} ") defer
  apply auto[1]
  apply (subgoal_tac "Max (insert 0 {y. y = get_value \<mu> a \<or> (\<exists>x\<in>set L. y = get_value \<mu> x)}) =
                     Max ({get_value \<mu> a} \<union> (insert 0 {y. \<exists>x\<in>set L. y = get_value \<mu> x}))")defer
  apply (metis Un_insert_right)
  apply (subgoal_tac " Max ({get_value \<mu> a} \<union> (insert 0 {y. \<exists>x\<in>set L. y = get_value \<mu> x})) = 
                      max (get_value \<mu> a) (Max (insert 0 {y. \<exists>x\<in>set L. y = get_value \<mu> x}))")
  apply presburger
  apply (case_tac "{y. \<exists>x\<in>set L. y = get_value \<mu> x} = {}")
  using finite.simps max.commute sup_bot_left sup_commute apply fastforce 
  by simp

lemma get_values_set_eq:" set L = B \<Longrightarrow> get_values \<mu> L = get_values_set \<mu> B"
  apply (simp add:get_values_set_def image_def)
  apply auto
  using get_values.elims apply blast
  using Collect_cong Un_commute get_values_set_eq_lemma by auto 


lemma R_closed_RL_lemma:
  "s1\<in> set(get_R_states r) \<Longrightarrow> f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r) \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>
   B\<in>(R_closed_set r f) \<Longrightarrow> get_values_set \<mu> B = get_values_set \<nu> B \<Longrightarrow> s1\<in>B \<Longrightarrow>
   ((get_value \<mu> s1) \<le> (get_values \<nu> (R_right r s1))) \<and>((get_value \<nu> s1) \<le> (get_values \<mu> (R_left r s1)))"
  apply (subgoal_tac "set (R_right r s1) = B \<and> set (R_left r s1) = B") defer
  apply (simp add: R_closed_set_relation)
  apply (subgoal_tac "s1\<in>B") defer
  apply simp
  using get_values_set_eq get_values_elims
  by metis

theorem R_closed_RL:"f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r) \<Longrightarrow>(get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow> 
        \<forall>B\<in>(R_closed_set r f). get_values_set \<mu> B = get_values_set \<nu> B \<Longrightarrow>
        \<forall>s1\<in> set(get_R_states r). ((get_value \<mu> s1) \<le> (get_values \<nu> (R_right r s1)))\<and>
                                  ((get_value \<nu> s1) \<le> (get_values \<mu> (R_left r s1)))"
  apply (subgoal_tac "\<forall>s\<in>set(get_R_states r). \<exists>B\<in>(R_closed_set r f). s\<in>B") defer
  apply (simp add: allstate_inR_closed_set get_R_states_set_list)
  apply (subgoal_tac "\<forall>B\<in>(R_closed_set r f). \<forall>s\<in>B. s\<in>set(get_R_states r)") defer
  apply (metis R_closed_set_allstate_inR get_R_states_set_list)
  apply auto
  apply (metis R_closed_set_relation get_values_elims get_values_set_eq)
  by (metis R_closed_set_relation get_values_elims get_values_set_eq)


lemma R_closed_RL_check:"f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>
                         \<forall>B \<in> (R_closed_set r f).  get_values_set \<mu> B = get_values_set \<nu> B \<Longrightarrow> RL_check r \<mu> \<nu>"
  apply (simp add: RL_check_def)
  by (simp add: R_closed_RL)

lemma Distr_equal_check_RL_check:"f\<noteq> [] \<Longrightarrow> equiv (allstates f) (set r) \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>
                                  B \<in> (R_closed_set r f) \<Longrightarrow>  Distr_equal_check r \<mu> \<nu>  f \<Longrightarrow> RL_check r \<mu> \<nu> "
  apply (simp add: Distr_equal_check_def)
  using R_closed_RL_check by auto

lemma Distr_equal_check_dl_RL_check_dl:"(s0,t0)\<in>set r \<Longrightarrow> f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f)\<Longrightarrow>
                                       (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). Distr_equal_check_dl r (get_distr f s0 a1) (get_distr f t0 a1)  f) \<Longrightarrow>
                                       (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). RL_check_dl r (get_distr f s0 a1) (get_distr f t0 a1)) "
  using Distr_equal_check_def Distr_equal_check_dl_def RL_check_dl_def R_closed_RL_check by fastforce


lemma RL_R_closed_lemma:"finite B\<Longrightarrow>\<forall>s1\<in>B. ((get_value \<mu> s1) \<le> get_values_set \<nu> B) \<and>((get_value \<nu> s1) \<le> get_values_set \<mu> B) \<Longrightarrow> get_values_set \<mu> B = get_values_set \<nu> B"
  apply (simp add: get_values_set_def) 
  by (smt (z3) Max.union Max_in Max_singleton finite_Un finite_imageI finite_insert image_iff image_is_empty max_def sup_bot.right_neutral)

theorem RL_R_closed:"f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>
        \<forall>s1\<in>set(get_R_states r). ((get_value \<mu> s1) \<le> (get_values \<nu> (R_right r s1)))\<and>
                                 ((get_value \<nu> s1) \<le> (get_values \<mu> (R_left r s1))) 
        \<Longrightarrow> \<forall>B\<in>(R_closed_set r f). get_values_set \<mu> B = get_values_set \<nu> B"
  apply (subgoal_tac "\<forall>s\<in>set(get_R_states r). \<exists>B\<in>(R_closed_set r f). s\<in>B") defer
  apply (simp add: allstate_inR_closed_set get_R_states_set_list)
  apply (subgoal_tac "\<forall>B1\<in>(R_closed_set r f). \<forall>s\<in>B1. s\<in>set(get_R_states r)") defer
  apply (metis R_closed_set_allstate_inR get_R_states_set_list)
  apply (subgoal_tac "\<forall>s1\<in>set(get_R_states r). \<exists>B\<in>(R_closed_set r f). set (R_right r s1) = B \<and> set (R_left r s1) = B") defer
  using R_closed_set_relation apply fastforce
  apply (subgoal_tac "\<forall>B\<in>(R_closed_set r f). \<forall>s1\<in>B. 
                      ((get_value \<mu> s1) \<le> get_values_set \<nu> B) \<and>((get_value \<nu> s1) \<le> get_values_set \<mu> B)") defer
  using R_closed_set_relation get_values_set_eq apply fastforce 
  by (meson R_closed_set_finite RL_R_closed_lemma)

lemma RL_check_R_closed:"f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>
                   RL_check r \<mu> \<nu> \<Longrightarrow> B \<in> (R_closed_set r f) \<Longrightarrow> get_values_set \<mu> B = get_values_set \<nu> B"
  apply (simp add: RL_check_def)
  by (simp add: RL_R_closed)

lemma RL_check_Distr_equal_check:"f\<noteq> [] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f) \<Longrightarrow>  RL_check r \<mu> \<nu> \<Longrightarrow> Distr_equal_check r \<mu> \<nu> f"
  using Distr_equal_check_def RL_check_R_closed by blast

lemma RL_check_dl_Distr_equal_check_dl:"(s0,t0)\<in>set r \<Longrightarrow> f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f)\<Longrightarrow>
                                       (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). RL_check_dl r (get_distr f s0 a1) (get_distr f t0 a1)) \<Longrightarrow>
                                       (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). Distr_equal_check_dl r (get_distr f s0 a1) (get_distr f t0 a1) f)"
  apply(simp add: RL_check_dl_def RL_check_def Distr_equal_check_dl_def Distr_equal_check_def)
  using RL_R_closed RL_check_def by fastforce

lemma BIS_R_correct1:"(s,t)\<in>set (BIS r1 r2 f) \<Longrightarrow>
                     \<forall>a1\<in>set(get_act (s,t) f (allact f)). RL_check_dl r2 (get_distr f s a1) (get_distr f t a1)"
  apply (induct r1 r2 f rule: BIS.induct)
  apply simp
  apply auto 
  by (smt (verit, ccfv_SIG) prod.inject set_ConsD surj_pair)

lemma BIS_R_correct:"r = BIS r1 r2 f \<Longrightarrow> (s,t)\<in>set r \<Longrightarrow>
                     \<forall>a1\<in>set(get_act (s,t) f (allact f)). RL_check_dl r2 (get_distr f s a1) (get_distr f t a1)"
  apply (induct r1 r2 f rule: BIS.induct)
   apply simp
 by (meson BIS_R_correct1)

lemma BIS_induct_R_correct:"r = BIS_induct r1 f \<Longrightarrow> (s,t)\<in>set r \<Longrightarrow>
                            (\<forall>a1\<in>set(get_act (s,t) f (allact f)). RL_check_dl r (get_distr f s a1) (get_distr f t a1))"
  apply (induct r1  f rule: BIS_induct.induct)
  apply simp 
  by (smt (verit) BIS_R_correct BIS_induct.simps(2) case_prod_conv surj_pair)                       

lemma BIS_induct_Distr_equal:"r= BIS_induct r1 f \<Longrightarrow> (s,t)\<in>set r \<Longrightarrow>  f\<noteq>[] \<Longrightarrow> equiv (allstates f) (set r)  \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f)\<Longrightarrow> 
                          (\<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r (get_distr f s a1) (get_distr f t a1)  f)"
  using BIS_induct_R_correct RL_check_dl_Distr_equal_check_dl by presburger

lemma BIS_R_closed_R_correct:"BIS_R_closed r1 r2 f \<Longrightarrow> (s,t)\<in>set r1 \<Longrightarrow>
                              (\<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1)  f)"
  apply (induct r1 r2 f rule:BIS_R_closed.induct)
  apply simp
  by (metis BIS_R_closed.simps(2) set_ConsD) 
 
lemma BIS_Distr_equal:"f\<noteq>[]\<Longrightarrow> equiv (allstates f) (set r) \<Longrightarrow> (get_R_states_set r)= (get_NFTS_states_set f)
                       \<Longrightarrow> r=r2 \<Longrightarrow>BIS r r2 f = r \<Longrightarrow> (s,t)\<in>set r  
                       \<Longrightarrow> (\<forall>a1\<in>set(get_act (s,t) f (allact f)). Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1) f)" 
  apply(subgoal_tac "\<forall>a1\<in>set(get_act (s,t) f (allact f)). RL_check_dl r2 (get_distr f s a1) (get_distr f t a1)") defer
  apply (metis BIS_R_correct)
  apply(simp add: RL_check_dl_def RL_check_def Distr_equal_check_dl_def Distr_equal_check_def)
  by (meson RL_R_closed)

lemma BIS_correct:
  assumes "f\<noteq>[]"
          "equiv (allstates f) (set r)"
          "(get_R_states_set r)= (get_NFTS_states_set f)"
          "r=r2"
  shows   "r = BIS r r2 f  \<Longrightarrow> BIS_R_closed r r2 f"
  apply (subgoal_tac "\<forall>(s,t)\<in>set r. (\<forall>a1\<in>set(get_act (s,t) f (allact f)).
                       Distr_equal_check_dl r2 (get_distr f s a1) (get_distr f t a1) f)") defer
  using BIS_Distr_equal assms(1) assms(2) assms(3) assms(4) apply force
  apply (induct r) 
  apply auto
  using RL_R_closed BIS_R_correct by (meson list.set_intros(1) set_subset_Cons)

theorem BIS_induct_correct:
  assumes "f\<noteq>[]"
          "equiv (allstates f) (set r)"
          "(get_R_states_set r)= (get_NFTS_states_set f)"
  shows   "r=BIS_induct r1 f \<Longrightarrow> BIS_R_closed r r f"
  using assms
  apply (induct r1 f rule:BIS_induct.induct)
  apply simp
  by (metis BIS_correct BIS_induct.simps(2))


theorem equivalence_R_correct: 
  assumes "f\<noteq>[]"
          "equiv (allstates f) (set r)"
          "(get_R_states_set r)= (get_NFTS_states_set f)"
  shows"r = equivalence_R f \<Longrightarrow> is_equivalence_R r f"
  using assms 
  by (simp add: BIS_induct_correct equivalence_R_def is_equivalence_R_def)

theorem RL_R_closed_eq:
  assumes "f\<noteq>[]"
          "equiv (allstates f) (set r)"
          "(get_R_states_set r)= (get_NFTS_states_set f)"
          "r=r2"
  shows "BIS_RL r r2 f \<Longrightarrow> BIS_R_closed r r2 f"
  apply (induct r)
  apply simp
  apply auto
  apply presburger
  apply (simp add:Distr_equal_check_dl_def RL_check_dl_def RL_check_def Distr_equal_check_def)
  by (metis RL_R_closed assms)

theorem R_closed_RL_eq:
  assumes "f\<noteq>[]"
          "equiv (allstates f) (set r)"
          "(get_R_states_set r)= (get_NFTS_states_set f)"
          "r=r2"
  shows "BIS_R_closed r r2 f \<Longrightarrow> BIS_RL r r2 f "
  apply (induct r)
  apply simp
  apply auto
  apply presburger 
  apply (simp add:Distr_equal_check_dl_def RL_check_dl_def RL_check_def Distr_equal_check_def)
  by (metis R_closed_RL assms)

end