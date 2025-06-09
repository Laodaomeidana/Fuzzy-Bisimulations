theory Bis_R_closed
  imports Complex_Main NFTS Bisimulation
begin

definition union_set::"State set set \<Rightarrow> State set" where
"union_set ss \<equiv> \<Union> ss"
value "union_set  {{''s''},{''t''},{''s1''},{}}"
value "union_set  {{''s'',''s2''},{''t''},{''s1''}}"

definition subset::"State \<Rightarrow> State set set \<Rightarrow> State set set" where
"subset s ss \<equiv>  {x\<in>ss. s\<in>x}"
value"subset ''s'' {{''s'',''t''},{''a''},{''s'',''b''}}"

lemma union_set_empty1:"union_set {{}} ={}"
  by (simp add : union_set_def)
lemma union_set_empty2:"union_set {} ={}"
  by (simp add : union_set_def)
lemma subset_empty1:"subset s {} = {}"
  by (simp add: subset_def union_set_def)
lemma subset_empty2:"subset s {{}} = {}"
  by (simp add: subset_def union_set_def)
lemma union_set_contains_all:
  "\<forall>s. (\<exists>S\<in>ss. s \<in>S) \<Longrightarrow> s \<in> union_set ss"
  by (auto simp: union_set_def)
lemma subset_included_in_union:
  "\<forall>s S. S \<in> ss \<and>s \<in> S \<Longrightarrow> S \<subseteq> subset s ss"
  by (auto simp: subset_def union_set_def)
lemma union_set_empty_iff:
  "union_set ss = {} \<Longrightarrow> (\<forall>S\<in>ss. S = {})"
  by (auto simp: union_set_def)
lemma subset_empty_iff:
  "subset s ss = {} \<longleftrightarrow> (\<forall>S\<in>ss. s \<notin> S)"
  by (auto simp: subset_def union_set_def)
lemma union_set_mono:
  "ss1 \<subseteq> ss2 \<Longrightarrow> union_set ss1 \<subseteq> union_set ss2"
  by (auto simp: union_set_def)
lemma subset_mono:
  "ss1 \<subseteq> ss2 \<Longrightarrow> subset s ss1 \<subseteq> subset s ss2"
  by (auto simp: subset_def union_set_def)
lemma union_set_union:
  "union_set (ss1 \<union> ss2) = union_set ss1 \<union> union_set ss2"
  by (auto simp: union_set_def)
lemma subset_union:
  "subset s (ss1 \<union> ss2) = subset s ss1 \<union> subset s ss2"
  by (auto simp: subset_def union_set_def)
lemma subset_subset:"union_set(subset a s) \<subseteq> union_set s"
  apply (simp add:subset_def union_set_def) by auto
lemma subset_union_subset:"union_set(subset a s) \<union>union_set(subset b s) \<subseteq> union_set s"
  apply (simp add:subset_def union_set_def) by auto
lemma subset_invariance:"union_set ((s - subset a s) \<union> {union_set (subset a s)}) = union_set s"
  apply (simp add:subset_def union_set_def) by blast
lemma notin_s:"x = (s - (subset s0 s) - (subset t0 s)) \<Longrightarrow> a\<in>(subset s0 s) \<Longrightarrow>b\<in>(subset t0 s)\<Longrightarrow> a\<notin>x \<longleftrightarrow>b\<notin>x"
  by (simp add:subset_def union_set_def)
lemma in_x:"x = (s - (subset s0 s) - (subset t0 s)) \<union> ({union_set (subset s0 s) \<union> union_set(subset t0 s)})\<Longrightarrow> 
            subset s0 x \<subseteq>x \<longleftrightarrow> subset t0 x \<subseteq> x"
  apply (simp add:subset_def union_set_def) by blast
lemma subset_correct1:"a\<in>(subset s0 s) \<Longrightarrow>s0\<in>a"
  by (simp add:subset_def union_set_def)
lemma subset_correct1_1:"(subset s0 s = subset t0 s) \<Longrightarrow> a\<in> subset s0 s \<Longrightarrow> s0\<in>a\<longleftrightarrow>t0\<in>a"
  using subset_correct1 by auto
lemma subset_correct2:"(subset s0 s)\<noteq>{} \<Longrightarrow>s0\<in>union_set (subset s0 s)"
  by (simp add:subset_def union_set_def)
lemma subset_correct3:"(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow>a=union_set (subset s0 s) \<union> union_set(subset t0 s) \<Longrightarrow> s0\<in>a\<longleftrightarrow> t0\<in>a "
  by (simp add:subset_def union_set_def)
lemma subset_correct4:"(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow>
       x = (s - (subset s0 s) - (subset t0 s)) \<union> ({union_set (subset s0 s) \<union> union_set(subset t0 s)}) \<Longrightarrow> 
       subset s0 x = {union_set (subset s0 s) \<union> union_set(subset t0 s)} "
  by (simp add:subset_def union_set_def) auto
lemma subset_correct5:"(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow>
       x = (s - (subset s0 s) - (subset t0 s)) \<union> ({union_set (subset s0 s) \<union> union_set(subset t0 s)}) \<Longrightarrow> subset s0 x = subset t0 x "
  by (simp add:subset_def union_set_def subset_correct4) auto
lemma subset_correct6:"(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow>
       x \<in> (s - (subset s0 s) - (subset t0 s)) \<union> ({union_set (subset s0 s) \<union> union_set(subset t0 s)}) \<Longrightarrow> s0\<in> x \<longleftrightarrow> t0\<in>x " 
  apply (simp add:subset_def union_set_def) by blast
lemma subset_correct7:"(subset s0 s) \<noteq> (subset t0 s)\<Longrightarrow>(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{} \<Longrightarrow>
       x \<in> (s - (subset s0 s) - (subset t0 s)) \<union> ({union_set (subset s0 s) \<union> union_set(subset t0 s)}) \<Longrightarrow> s0\<in> x \<longleftrightarrow> t0\<in>x " 
  apply(simp add:subset_def union_set_def) by blast 
lemma subset_correct8:"subset s0 s = subset t0 s \<Longrightarrow> s'=((s-(subset s1 s)-(subset t1 s)) \<union> ({union_set(subset s1 s) \<union> union_set(subset t1 s)}))
        \<Longrightarrow> subset s0 s' = subset t0 s'"
  by (auto simp add: union_set_def subset_def)


fun get_Distr_states_set ::"Distr \<Rightarrow>State set set"where
"get_Distr_states_set [] = {}"|
"get_Distr_states_set (x#xs) = {{snd x}}\<union> get_Distr_states_set xs"

fun get_NFTS_states_set::"NFTS \<Rightarrow> State set set" where
"get_NFTS_states_set [] = {}"|
"get_NFTS_states_set (x#xs) = {{fst x}} \<union> (get_Distr_states_set (snd (snd x))) \<union> get_NFTS_states_set xs"
value"get_NFTS_states_set NFTS1"

lemma get_Dsitr_states_set_subset:
  "\<forall>x \<in>set d. {snd x} \<in> get_Distr_states_set d"
  by (induction d, auto)
lemma get_NFTS_states_set_subset:
  "\<forall>x \<in> set f. {fst x} \<in> get_NFTS_states_set f \<and>  (get_Distr_states_set (snd (snd x)) \<subseteq> get_NFTS_states_set f )"
  by (induction f, auto)
lemma get_Dsitr_states_set_Cons:
  "get_Distr_states_set (d1 @ d2) = get_Distr_states_set d1 \<union> get_Distr_states_set d2"
  by (induction d1, auto)
lemma get_NFTS_states_set_Cons:
  "get_NFTS_states_set (f1 @ f2) = get_NFTS_states_set f1 \<union> get_NFTS_states_set f2"
  by (induction f1, auto)
lemma get_NFTS_states_set_notempty:"f\<noteq>[] \<Longrightarrow> (get_NFTS_states_set f) \<noteq>{} \<and> get_NFTS_states_set f \<noteq>{{}}"
  by (induct f,auto)
lemma get_Distr_states_set_card:"\<forall>x\<in>(get_Distr_states_set u). card x = 1"
  by (induct u) auto
lemma get_NFTS_states_set_card:"\<forall>x\<in>(get_NFTS_states_set f). card x = 1"
  by (induct f) (auto simp add: get_Distr_states_set_card)
lemma get_Distr_and_R_states_eq:
  "set (get_R_states r)= \<Union>(get_Distr_states_set u) \<Longrightarrow>  x\<in>set (get_R_states r) \<longleftrightarrow> {x}\<in>(get_Distr_states_set u)"
  using get_Distr_states_set_card get_R_states_setset by force
lemma get_NFTS_and_R_states_eq:
  "set (get_R_states r)= \<Union>(get_NFTS_states_set f) \<Longrightarrow>  x\<in>set (get_R_states r) \<longleftrightarrow> {x}\<in>(get_NFTS_states_set f)"
  using get_NFTS_states_set_card get_R_states_setset by force


fun get_R_states_set::"R\<Rightarrow>State set set" where
"get_R_states_set [] ={}"|
"get_R_states_set ((s,t)#xs) = {{s}} \<union> {{t}} \<union> get_R_states_set xs"

fun partition_not_inR::"R \<Rightarrow> State set set\<Rightarrow> State set set" where
"partition_not_inR [] s = (if s\<noteq>{} then {union_set s} else {})"|
"partition_not_inR (x#xs) s = partition_not_inR xs (s-{{fst x}}-{{snd x}})"

lemma get_R_states_list_set_elem:"s1 \<in> set (get_R_states r) \<longleftrightarrow> {s1}\<in> get_R_states_set r"
  by (induct r rule: get_R_states_set.induct) auto 
lemma get_R_states_set_app:" get_R_states_set (xs @ys) =get_R_states_set xs \<union> get_R_states_set ys"
  by (induct xs) auto
lemma get_R_statses_set_correct:" s=get_R_states_set r \<Longrightarrow> (s0, t0)\<in>set r \<Longrightarrow> {s0} \<in> s \<and> {t0}\<in>s"
  by (induct r arbitrary:s) auto
lemma get_R_states_set_inv:"r=(s0,t0)#xs \<Longrightarrow> (s0,t0)\<in>set xs \<Longrightarrow> get_R_states_set r =get_R_states_set xs"
  apply auto
  by (simp_all add: get_R_statses_set_correct)
lemma get_R_states_set_notempt:"(s0,t0) \<in> set r  \<Longrightarrow> s=get_R_states_set r \<Longrightarrow>subset s0 s\<noteq>{} \<and> (subset t0 s)\<noteq>{}"
  apply (simp add: union_set_def subset_def)
  apply (induct r arbitrary :s)
  apply simp_all
  apply auto
  by auto
lemma get_R_states_set_subset:" s0 \<in> x \<Longrightarrow> x \<in> get_R_states_set xs \<Longrightarrow> x= {s0}"
  by (induct xs) auto
lemma get_R_states_subset_correct_lemma1 :"(s0,t0) \<in> set r  \<Longrightarrow> s=get_R_states_set r \<Longrightarrow>  {{s0}} \<subseteq> subset s0 s "
  by (simp add: get_R_statses_set_correct union_set_def subset_def)
lemma get_R_states_subset_correct_lemma2 :" (s0,t0) \<in> set r  \<Longrightarrow> s=get_R_states_set r \<Longrightarrow>  subset s0 s \<subseteq> {{s0}} "
  apply (induct r rule:get_R_states_set.induct )
  apply auto
  apply (simp_all add: union_set_def subset_def)
  apply auto
  using get_R_states_set_subset apply blast
  using get_R_states_set_subset by blast 
lemma get_R_states_subset_correct :"(s0,t0) \<in> set r  \<Longrightarrow> s=get_R_states_set r \<Longrightarrow>  subset s0 s = {{s0}}"
  by (meson get_R_states_subset_correct_lemma1 get_R_states_subset_correct_lemma2 subset_antisym)
lemma get_R_states_set_card:"\<forall>x\<in>(get_R_states_set u). card x = 1"
  by (induct u) auto
lemma "(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow> s=get_R_states_set r \<Longrightarrow>  subset s0 s =subset t0 s  \<Longrightarrow> s0=t0"
  apply (induct r)
  apply (simp add: subset_empty1)
  apply auto
  apply (simp_all add: union_set_def subset_def)
  by (smt (verit, ccfv_threshold) Collect_empty_eq get_R_states_set.simps(1) get_R_states_set_subset insertE mem_Collect_eq singleton_iff)
lemma get_R_states_set_list:"set (get_R_states r) = \<Union> (get_R_states_set r)"
  by (induct r) auto


definition partition_init::"R \<Rightarrow>State set set \<Rightarrow>State set set"where
"partition_init r s = (if s \<noteq> {} then partition_not_inR r s \<union> get_R_states_set r else get_R_states_set r)"
value"partition_init  [(''s'',''t'')] {{''s''},{''t''},{''s1''},{''s2''},{''s3''}}"
value"partition_init  [(''s'',''t'')] {{''s''},{''t''}}"
value"partition_init  [(''s'',''t'')] {}"
value"partition_init [(''s'',''t''),(''s1'',''s2'')] {{''s''},{''t''},{''s1''},{''s2''},{''s3''},{''s4''}}"

fun partition::"R\<Rightarrow> State set set \<Rightarrow> State set set" where
"partition [] s =  s"|
"partition (x#xs) s  = 
 (if(subset (fst x) s = subset (snd x) s) then partition xs s 
 else partition xs ((s-(subset (fst x) s)-(subset (snd x) s)) \<union> ({union_set(subset (fst x) s) \<union> union_set(subset (snd x) s)})))" 


definition R_closed_set::"R \<Rightarrow> NFTS \<Rightarrow> State set set" where
"R_closed_set r f \<equiv> partition r (partition_init r (get_NFTS_states_set f))"
value"R_closed_set [(''s'',''t''),(''s2'',''s3'')] NFTS1"

value"partition [(''s'',''t'')] {{''s''},{''t''},{''s1''}}"
value"partition [(''s'',''t'')] {}"
value"partition [(''s'',''t''),(''s1'',''s2'')] {{''s''},{''t''},{''s1''}}"
value"partition [(''s'',''t''),(''s1'',''s2''),(''s'',''s1'')] {{''s''},{''t''},{''s1''},{''s2''},{''s3''},{''s4''},{''s5''}}"
value"partition [(''s'',''t''),(''s1'',''s2'')] (partition_init [(''s'',''t''),(''s1'',''s2'')] {{''s''},{''t''},{''s1''},{''s2''},{''s3''},{''s4''},{''s5''}})"

lemma partition_not_inR_Sempty :"partition_not_inR r {} = {}"
  by (induct r) auto
lemma partition_not_inR_Rempty1 :"s\<noteq>{} \<Longrightarrow> partition_not_inR [] s = {union_set s}"
  by simp
lemma partition_not_inR_Rempty2 :"s={} \<Longrightarrow> partition_not_inR [] s = s"
  by simp
lemma partition_init_Rempty:"s\<noteq>{} \<Longrightarrow> partition_init [] s =  {union_set s} "
  by (simp add: partition_init_def)
lemma partition_init_Sempty:" partition_init r {} = get_R_states_set r"
  by (simp add: partition_init_def)
lemma partition_Sempty:"s={} \<Longrightarrow>  (partition r s) = {}"
  apply (induct r s rule: partition.induct)
  by (simp_all add: subset_empty1)

lemma partition_not_inR_subset1:"union_set (partition_not_inR r s) \<subseteq> union_set s"
  apply (induction r s rule: partition_not_inR.induct)
  apply (simp add: union_set_def)
  by (metis Diff_subset dual_order.trans partition_not_inR.simps(2) union_set_mono)
lemma partition_not_inR_subset2:"x\<in>(partition_not_inR r s) \<Longrightarrow> x\<subseteq> union_set  s"
  apply (induct r s rule: partition_not_inR.induct)
  apply (simp add: union_set_def)
  apply (metis empty_iff insertE set_eq_subset union_set_def)
  by (metis Diff_subset dual_order.trans partition_not_inR.simps(2) union_set_mono)
lemma partition_init_subset:"s\<noteq>{} \<Longrightarrow> get_R_states_set r \<subseteq> s \<Longrightarrow>x \<in> (partition_init r s) \<Longrightarrow> x\<subseteq> union_set s"
  apply (simp add:partition_init_def)
  by (metis Union_upper in_mono partition_not_inR_subset2 union_set_def)

lemma partition_not_inR_Ssubempty:"s1\<subseteq>s \<Longrightarrow> partition_not_inR r s = {} \<Longrightarrow> partition_not_inR r s1 = {}"
  apply (induct r arbitrary:s s1)
  apply (metis insert_not_empty partition_not_inR.simps(1) subset_empty)
  apply (subgoal_tac"partition_not_inR (a # r) s = partition_not_inR r (s - {{fst a}} - {{snd a}})") defer
  apply (meson partition_not_inR.simps(2))
  apply (subgoal_tac"partition_not_inR (a # r) s1 = partition_not_inR r (s1 - {{fst a}} - {{snd a}})") defer
  apply (meson partition_not_inR.simps(2))
  apply (subgoal_tac" (s1 - {{fst a}} - {{snd a}}) \<subseteq> (s - {{fst a}} - {{snd a}}) ") defer
  by auto
lemma partition_not_inR_Rsubempty:"  partition_not_inR r s = {} \<Longrightarrow> partition_not_inR (a#r) s = {}"
  apply (induct r arbitrary:s)
  apply simp
  apply (metis (full_types) empty_Diff empty_subsetI insert_not_empty)
  apply (subgoal_tac"partition_not_inR (a # aa # r) s =partition_not_inR (aa # r) (s - {{fst a}} - {{snd a}}) ") defer
  using partition_not_inR.simps(2) apply blast
  apply (subgoal_tac" (s - {{fst a}} - {{snd a}}) \<subseteq> s ") defer
  apply blast
  using partition_not_inR_Ssubempty by presburger
lemma partition_not_inR_nonempty:"\<forall>x\<in>s. card x = 1 \<Longrightarrow> partition_not_inR r s \<noteq> {{}}"
  apply (induct r arbitrary:s)
  apply (metis all_not_in_conv card_1_singletonE insert_not_empty partition_not_inR.simps(1) the_elem_eq union_set_empty_iff)
  apply (subgoal_tac "partition_not_inR (a # r) s = partition_not_inR r (s-{{fst a}}-{{snd a}})")
  apply simp
  by (meson partition_not_inR.simps(2))

lemma Union_del_eq:
  assumes "\<forall>x\<in>s. card x = 1"
  shows "\<Union>s - {a} - {b} = \<Union>(s - {{a}} - {{b}})"
proof
  show "\<Union>s - {a} - {b} \<subseteq> \<Union>(s - {{a}} - {{b}})" by blast
  show "\<Union>(s - {{a}} - {{b}}) \<subseteq> \<Union>s - {a} - {b}"
  proof
    fix x  assume "x \<in> \<Union>(s - {{a}} - {{b}})"
    then obtain X where "X \<in> s - {{a}} - {{b}}" and "x \<in> X" by auto
    then have "X \<in> s" and "X \<noteq> {a}" and "X \<noteq> {b}" by auto
    then have "X - {a} - {b} = X" apply auto
    by (metis assms card_1_singletonE empty_iff insert_iff)+
    with \<open>x \<in> X\<close> and \<open>X \<in> s\<close> have "x \<in> \<Union>s - {a} - {b}" by auto
    thus "x \<in> \<Union>s - {a} - {b}" .
  qed
qed

lemma partition_not_inR_correct_lemma1:"\<forall>x\<in>s. card x = 1 \<Longrightarrow> \<Union> (partition_not_inR r s) = \<Union>s - set (get_R_states r)" 
  apply (induct r arbitrary:s)
  using union_set_def apply auto[1]
  apply (subgoal_tac "partition_not_inR (a # r) s = partition_not_inR r (s-{{fst a}}-{{snd a}})")  defer
  apply simp
  apply (subgoal_tac "\<Union>s - set (get_R_states (a # r)) =\<Union>(s-{{fst a}}-{{snd a}}) - set (get_R_states r) ")
  apply auto[1]
  apply (subgoal_tac "\<Union>s - {fst a} - {snd a} = \<Union>(s-{{fst a}}-{{snd a}}) ")
  apply (metis Diff_insert2 get_R_states.simps(2) list.simps(15))
  by (meson Union_del_eq) 
 
lemma partition_not_inR_correct_lemma2:"\<forall>x\<in>s. card x = 1 \<Longrightarrow> set (get_R_states r)= \<Union>s \<Longrightarrow> partition_not_inR r s = {}"
  apply (subgoal_tac"\<Union>s - set (get_R_states r) = {}")defer
  apply simp
  apply (subgoal_tac "\<Union>(partition_not_inR r s) = {}") defer
  apply (simp add: partition_not_inR_correct_lemma1)
  apply (subgoal_tac "(partition_not_inR r s) \<noteq> {{}}")
  apply auto[1]
  by (simp add: partition_not_inR_nonempty)

lemma partition_not_inR_correct:"f\<noteq>[] \<Longrightarrow> s=(get_NFTS_states_set f) \<Longrightarrow> set (get_R_states r)=\<Union> s \<Longrightarrow> 
                          partition_not_inR r s = {}"
  apply (subgoal_tac"s \<noteq>{} \<and> s \<noteq>{{}}") defer
  apply (simp add: get_NFTS_states_set_notempty)
  apply (induct r  arbitrary: s  )
  using empty_set equals0I get_R_states_empty insertI1 apply force
  apply (subgoal_tac "partition_not_inR (a # r) s = partition_not_inR r (s-{{fst a}}-{{snd a}})")  defer
  apply (meson partition_not_inR.simps(2))
  apply (subgoal_tac "\<forall>x\<in>s. card x = 1") defer
  apply (metis get_NFTS_states_set_card)
  apply (subgoal_tac "\<forall>x\<in>set (get_R_states r). {x}\<in>s") defer
  apply (meson get_NFTS_and_R_states_eq get_R_states_subset in_mono)
  by (meson partition_not_inR_correct_lemma2)

lemma partition_init_correct:"f\<noteq>[] \<Longrightarrow> s= (get_NFTS_states_set f)\<Longrightarrow> (get_R_states_set r)=s\<Longrightarrow> partition_init r s = s"
  by (simp add: get_R_states_set_list partition_not_inR_correct get_NFTS_states_set_notempty partition_init_def) 
  
lemma partition_invariance: "union_set (partition r s) = union_set s"
proof (induction r arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?s1 = "subset (fst x) s"
  let ?s2 = "subset (snd x) s"
  have "union_set (partition (x # xs) s) = 
         (if ?s1 = ?s2 then union_set (partition xs s)
          else union_set (partition xs ((s - ?s1 - ?s2) \<union> {union_set (subset (fst x) s) \<union> union_set(subset (snd x) s)})))"
    by simp
  also have "... = (if ?s1 = ?s2 then union_set s else union_set ((s - ?s1 - ?s2) \<union> {union_set (subset (fst x) s) \<union> union_set(subset (snd x) s)}))"
    using local.Cons union_set_union by presburger
  also have "... = (if ?s1 = ?s2 then union_set s else union_set s)"
    apply (simp add:union_set_def union_set_union subset_def)
    by blast
  finally show ?case
    by simp 
qed
lemma partition_subset:" x \<in> (partition r s) \<Longrightarrow> x \<subseteq> \<Union> s"
  apply (induct r arbitrary:s)
  using union_set_def apply auto[1]
  by (metis Bis_R_closed.partition.simps(2) partition_invariance union_set_def)
  
lemma partition_get_R_states_set:" B \<in> partition r s \<Longrightarrow> s=(get_R_states_set r) \<Longrightarrow> s0\<in>B \<Longrightarrow> {s0}\<in>s"
  apply (subgoal_tac "B\<subseteq> union_set s") defer
  apply (simp add: partition_subset)
  apply (subgoal_tac "\<forall>a\<in>s. card a = 1")
  apply (simp add: partition_subset union_set_def)
  using get_R_states_set_card apply auto[1]
  using get_R_states_list_set_elem get_R_states_set_list union_set_def by auto
 
lemma partition_get_R_states_set2:" B \<in> partition r (s - subset s0 s -subset t0 s \<union> {union_set (subset s0 s) \<union> union_set (subset t0 s)})
                                    \<Longrightarrow> s=(get_R_states_set r) \<Longrightarrow> s0\<in>B \<Longrightarrow> {s0}\<in>s"
  apply (subgoal_tac "\<Union>(s - subset s0 s -subset t0 s \<union> {union_set (subset s0 s) \<union> union_set (subset t0 s)}) = \<Union>s") defer
  apply (metis Un_Diff_cancel2 Un_commute Un_left_commute ccpo_Sup_singleton subset_invariance union_set_def union_set_union)
  by (metis UnionI get_R_states_list_set_elem get_R_states_set_list partition_invariance union_set_def)

lemma R_closed_set_Rempty1:"get_NFTS_states_set f \<noteq>{} \<Longrightarrow> R_closed_set [] f = {union_set (get_NFTS_states_set f)}"
  by (simp add: R_closed_set_def partition_init_def)
lemma R_closed_set_Rempty2:"get_NFTS_states_set f = {} \<Longrightarrow> R_closed_set [] f =  (get_NFTS_states_set f)"
  by (simp add: R_closed_set_def partition_init_def)
lemma R_closed_set_Sempty:"R_closed_set r [] = partition r (get_R_states_set r)"
  by (simp add: R_closed_set_def partition_Sempty partition_init_Sempty)
lemma R_closed_subset:" get_R_states_set r \<subseteq> get_NFTS_states_set f \<Longrightarrow>x \<in> (R_closed_set r f) \<Longrightarrow> x \<subseteq> \<Union> (get_NFTS_states_set f)"
  apply (simp add:R_closed_set_def union_set_def partition_init_def)
  by (smt (z3) Union_Un_distrib order_subst1 partition_not_inR_subset1 partition_subset subset_Un_eq subset_refl sup_mono union_set_def)

lemma partition_correct_eq:" subset s0 s = subset t0 s \<Longrightarrow> B \<in> partition r s \<Longrightarrow> s0\<in>B \<longleftrightarrow> t0\<in>B"
  apply (induct r arbitrary:s)
  apply (simp add: union_set_def subset_def)
  apply blast
  apply (case_tac "subset (fst a) s = subset (snd a) s")
  apply (subgoal_tac "partition (a # r) s = partition r s")
  apply simp
  apply simp
  apply (subgoal_tac "partition (a # r) s = 
                     partition r ((s-(subset (fst a) s)-(subset (snd a) s)) \<union> ({union_set(subset (fst a) s) \<union> union_set(subset (snd a) s)}))")
  defer  apply simp  
  apply (subgoal_tac "subset s0 ((s-(subset (fst a) s)-(subset (snd a) s))\<union>({union_set(subset (fst a) s)\<union>union_set(subset (snd a) s)}))
                     =subset t0 ((s-(subset (fst a) s)-(subset (snd a) s)) \<union> ({union_set(subset (fst a) s) \<union> union_set(subset (snd a) s)}))")
  defer apply (meson subset_correct8) defer 
  by auto

lemma partition_correct_uneq:
    "(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow> subset s0 s \<noteq> subset t0 s \<Longrightarrow>  
      B\<in> partition r (s - subset s0 s -subset t0 s \<union> {union_set (subset s0 s) \<union> union_set (subset t0 s)}) \<Longrightarrow> s0\<in>B \<longleftrightarrow> t0\<in>B"
   apply (subgoal_tac "subset s0 ((s-(subset s0 s)-(subset t0 s))\<union>({union_set(subset s0 s)\<union>union_set(subset t0 s)}))
                      =subset t0 ((s-(subset s0 s)-(subset t0 s)) \<union> ({union_set(subset s0 s) \<union> union_set(subset t0 s)}))")
   defer apply (meson subset_correct5)
   using partition_correct_eq by blast
  
lemma partition_correct_lemma: 
  assumes"(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}"
  shows"x \<in> (if subset s0 s = subset t0 s then partition xs s
             else partition xs (s - subset (fst (s0, t0)) s -subset (snd (s0, t0)) s \<union>
                               {union_set (subset (fst (s0, t0)) s) \<union> union_set (subset (snd (s0, t0)) s)})) \<Longrightarrow>s0 \<in> x \<longleftrightarrow> t0 \<in> x"
  apply auto
  apply (case_tac "subset s0 s = subset t0 s")
  apply (subgoal_tac "x\<in>partition xs s")
  defer apply simp
  apply (subgoal_tac "x\<in>partition xs (s - subset (fst (s0, t0)) s -subset (snd (s0, t0)) s \<union>
                                     {union_set (subset (fst (s0, t0)) s) \<union> union_set (subset (snd (s0, t0)) s)})") defer
  apply simp defer
  using partition_correct_eq apply blast
  apply (simp add: partition_correct_uneq)
  apply (case_tac "subset s0 s = subset t0 s")
  apply (subgoal_tac "x\<in>partition xs s") defer
  apply simp
  apply (subgoal_tac "x\<in>partition xs (s - subset (fst (s0, t0)) s -subset (snd (s0, t0)) s \<union>
                                     {union_set (subset (fst (s0, t0)) s) \<union> union_set (subset (snd (s0, t0)) s)})") defer
  apply simp defer
  apply (simp_all add: partition_correct_uneq)
  using assms partition_correct_uneq apply auto[1]
  by (metis assms fst_conv partition_correct_eq partition_correct_uneq snd_conv)

lemma partition_correct_s0t0:
  "(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{} \<Longrightarrow>(s0, t0) \<in> set r  \<Longrightarrow> x \<in> partition r s \<Longrightarrow> s0 \<in> x \<Longrightarrow> t0 \<in> x"
  apply (induct r arbitrary:s)
  apply simp
  apply auto
  using partition_correct_lemma apply fastforce 
  apply (case_tac "subset a s = subset b s")
  apply (subgoal_tac "x\<in>partition r s")
  apply blast
  apply simp
  apply (subgoal_tac "x\<in>partition r (s - Bis_R_closed.subset (fst (a, b)) s - Bis_R_closed.subset (snd (a, b)) s 
                             \<union> {union_set (Bis_R_closed.subset (fst (a, b)) s) \<union> union_set (Bis_R_closed.subset (snd (a, b)) s)})")
  apply (simp_all add: union_set_def subset_def )
  by (smt (verit, ccfv_SIG) Diff_iff Sup_insert Un_Diff_cancel Un_assoc Un_iff UnionE Union_Un_distrib Union_iff insertI1 insert_iff mem_Collect_eq)

lemma partition_correct_t0s0:
   "(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{} \<Longrightarrow>(s0, t0) \<in> set r  \<Longrightarrow> x \<in> partition r s \<Longrightarrow> t0 \<in> x \<Longrightarrow> s0 \<in> x"
  apply (induct r arbitrary:s)
  apply simp
  apply auto
  using partition_correct_lemma apply fastforce 
  apply (case_tac "subset a s = subset b s")
  apply (subgoal_tac "x\<in>partition r s")
  apply blast
  apply simp
  apply (subgoal_tac "x\<in>partition r (s - Bis_R_closed.subset (fst (a, b)) s - Bis_R_closed.subset (snd (a, b)) s 
                             \<union> {union_set (Bis_R_closed.subset (fst (a, b)) s) \<union> union_set (Bis_R_closed.subset (snd (a, b)) s)})")
  apply (simp_all add: union_set_def subset_def) 
  by (smt (verit, ccfv_SIG) Diff_iff Sup_insert Un_Diff_cancel Un_assoc Un_iff UnionE Union_Un_distrib Union_iff insertI1 insert_iff mem_Collect_eq)

lemma partition_subset_correct:
  assumes "(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{} "
  shows "(s0,t0) \<in> set r \<Longrightarrow> R_set = partition r s \<Longrightarrow> subset s0 R_set = subset t0 R_set"
  apply auto 
  apply (simp_all add: union_set_def subset_def )
  using assms  apply (simp add: partition_correct_s0t0)
  using assms partition_correct_t0s0 by auto 

lemma partition_correct:"(subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow> B \<in> partition r s \<Longrightarrow> (s0,t0) \<in> set r \<Longrightarrow> s0 \<in> B \<longleftrightarrow> t0 \<in> B"
  using partition_correct_s0t0 partition_correct_t0s0 by blast 

lemma R_closed_set_correct:"s=(partition_init r (get_NFTS_states_set f)) \<Longrightarrow>
                           (subset s0 s)\<noteq>{} \<and> (subset t0 s)\<noteq>{}\<Longrightarrow>B\<in>R_closed_set r f \<Longrightarrow> (s0,t0)\<in>set r\<Longrightarrow> s0\<in>B \<longleftrightarrow> t0\<in>B"
  apply (simp add:R_closed_set_def )
  by (simp add: partition_correct)

definition Distr_equal_check::"R \<Rightarrow> Distr \<Rightarrow> Distr \<Rightarrow>  NFTS \<Rightarrow> bool"where
"Distr_equal_check r \<mu> \<nu> f \<equiv> \<forall>B \<in> (R_closed_set r f). get_values_set \<mu> B = get_values_set \<nu> B"

definition Distr_equal_check_dl::"R \<Rightarrow>  Distr list \<Rightarrow> Distr list \<Rightarrow> NFTS \<Rightarrow> bool" where
"Distr_equal_check_dl r d1 d2 f \<equiv> d1\<noteq>[]\<and>d2\<noteq>[]\<and>(\<forall>\<mu>\<in>set d1.  \<exists>\<nu>\<in> set d2.  Distr_equal_check r \<mu> \<nu> f)"

fun BIS_R_closed::"R \<Rightarrow> R \<Rightarrow> NFTS \<Rightarrow> bool" where
"BIS_R_closed [] _ _= True"|
"BIS_R_closed ((s0,t0)#xs) r f = (if ((\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). 
                                       Distr_equal_check_dl r (get_distr f s0 a1) (get_distr f t0 a1)  f)) 
                                  then (True\<and>BIS_R_closed xs r f) 
                                  else False)"


definition is_equivalence_R ::"R \<Rightarrow> NFTS \<Rightarrow> bool"where
"is_equivalence_R R f \<equiv> BIS_R_closed R R f"

lemma get_R_states_set_correct2:"B\<in>(get_R_states_set r) \<Longrightarrow> s1\<in>B \<Longrightarrow> \<exists>(a,b)\<in>set r. a=s1\<or> b= s1"
  by (induct r) auto 
lemma get_R_states_set_finite:"finite (get_R_states_set r) "
  by (induct r rule:get_R_states_set.induct ) auto
lemma get_R_states_set_elems_finite:"s=(get_R_states_set r) \<Longrightarrow> B\<in>s \<Longrightarrow>finite B"
  by (metis all_not_in_conv finite.simps get_R_states_set_subset)
lemma get_R_states_set_subset_finite:"s=(get_R_states_set r) \<Longrightarrow> finite (subset a s)"
  by (simp add: subset_def union_set_def get_R_states_set_finite)
lemma get_R_states_set_card1:"s=(get_R_states_set r) \<Longrightarrow> B\<in>s \<Longrightarrow>card B =1"
  by (simp add: get_R_states_set_card)
lemma partition_elem_finite:"B \<in> partition r s \<Longrightarrow> s = (get_R_states_set r) \<Longrightarrow>finite B"
  apply (subgoal_tac "B\<subseteq> (\<Union>s)") defer
  apply (simp add: partition_subset)
  by (meson finite_Union get_R_states_set_elems_finite get_R_states_set_finite rev_finite_subset)
lemma partition_finite:" s = (get_R_states_set r) \<Longrightarrow>finite (partition r s)"
  apply (subgoal_tac "\<Union>(partition r s) = \<Union> s")
  apply (metis finite_Union finite_UnionD get_R_states_set_elems_finite get_R_states_set_finite)
  using partition_invariance union_set_def by auto

lemma get_R_states_set_subsetfst_card:" x\<in> (set r) \<Longrightarrow> card (subset (fst x) (get_R_states_set r)) =1"
  apply (subgoal_tac "{fst x} \<in> (get_R_states_set r)")
  apply (metis get_R_states_subset_correct is_singletonI is_singleton_altdef prod.collapse)
  by (metis eq_fst_iff get_R_statses_set_correct)
lemma get_R_states_set_subsetsnd_card:" x\<in> (set r) \<Longrightarrow> card (subset (snd x) (get_R_states_set r)) =1"
  apply (subgoal_tac "{snd x} \<in> (get_R_states_set r)") defer
  apply (metis get_R_statses_set_correct prod.exhaust_sel)
  apply (subgoal_tac "(subset (snd x) (get_R_states_set r)) = {{snd x}}")
  apply simp
  apply (simp add:subset_def union_set_def)
  using get_R_states_set_subset by force
lemma get_R_states_set_fst_subset_in:"x\<in> (set r) \<Longrightarrow> s=(get_R_states_set r) \<Longrightarrow> union_set (subset (fst x) s) \<in> s"
  apply (subgoal_tac "card (subset (fst x) s) =1 \<and> finite (subset (fst x) s)")
  apply (simp add: subset_def union_set_def)
  apply (metis (no_types, lifting) card_1_singleton_iff ccpo_Sup_singleton mem_Collect_eq singletonI)
  by (simp add: get_R_states_set_subset_finite get_R_states_set_subsetfst_card)
lemma get_R_states_set_snd_subset_in:"x\<in> (set r) \<Longrightarrow> s=(get_R_states_set r) \<Longrightarrow> union_set (subset (snd x) s) \<in> s  "
  apply (subgoal_tac "card (subset (snd x) s) =1 \<and> finite (subset (snd x) s)")
  apply (simp add: subset_def union_set_def)
  apply (metis (no_types, lifting) card_1_singleton_iff ccpo_Sup_singleton mem_Collect_eq singletonI)
  by (simp add: get_R_states_set_subset_finite get_R_states_set_subsetsnd_card)

end