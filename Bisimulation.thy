theory Bisimulation
  imports Complex_Main NFTS
begin

type_synonym R = "(State \<times> State) list"
type_synonym RL = "(Distr \<times> Distr) list"

definition "R1::R  \<equiv>[(''s'',''t''),(''s1'',''s1''),(''s1'',''s2''),(''s2'',''s1''),(''s3'',''s2''),(''s3'',''s3'')] " 
definition "R2::R  \<equiv>[(''s'',''t''),(''t'',''s'')] "

fun init_R_State::"State \<Rightarrow> State list \<Rightarrow> R" where
"init_R_State s [] = []"|
"init_R_State s (x#xs) = (s,x)#init_R_State s xs"
fun init_R_list ::"State list \<Rightarrow> State list \<Rightarrow> R" where
"init_R_list [] s = []"|
"init_R_list (x#xs) s = init_R_State x s @ init_R_list xs s"
value"init_R_list (allstates_list [(''s1'',''a'',[(0.7,''t11''),(0.6,''t12''),(0.5,''t13'')]),
                          (''s1'',''a'',[(0.3,''t14''),(0.7,''t15''),(0.1,''t16'')]), 
                          (''t12'',''b'',[(0.7,''v11''),(0.6,''v12'')])]) 
                  (allstates_list [(''s2'',''a'',[(0.7,''t21''),(0.6,''t22''),(0.5,''t23'')]),
                          (''s2'',''a'',[(0.3,''t24''),(0.7,''t25''),(0.1,''t26'')]),
                          (''t22'',''b'',[(0.7,''v21'')])])"

lemma init_R_State_empty:
  "init_R_State s [] = []" by simp
lemma init_R_list_empty:
  "init_R_list [] s  =  []" by simp
lemma init_R_State_subset:
  "snd ` set (init_R_State s xs) \<subseteq> set xs"
  by (induct xs) auto
lemma init_R_State_Cons:
  "init_R_State s (xs@ys) = (init_R_State s xs) @ (init_R_State s ys)"
  apply (induct xs)
  by simp_all
lemma init_R_list_subset:
  "snd ` set (init_R_list xs ys) \<subseteq> set ys"
  apply (induct xs ys rule:init_R_list.induct)
  apply auto
  by (metis image_subset_iff init_R_State_subset snd_conv)
lemma init_R_list_Cons:
"init_R_list (xs@ys) s = (init_R_list xs s) @ (init_R_list ys s)"
  apply (induct xs)
  apply simp_all
  done
(*lemma init_R_list_equiv:"s\<noteq>{} \<Longrightarrow>r = s\<times>s \<Longrightarrow> equiv s r"
  apply (simp add: equiv_def)
  apply auto
  apply (simp add: refl_onI)
  apply (simp add: converse_Times sym_conv_converse_eq)
  by (metis SigmaD1 SigmaD2 SigmaI transI)
*)
lemma init_R_list_equiv:
  assumes "s \<noteq> {}" and "r = s \<times> s"
  shows "equiv s r"
proof -
  have "refl_on s r"
  proof show "r \<subseteq> s \<times> s" using \<open>r = s \<times> s\<close> by simp
  next show " \<And>x. x \<in> s \<Longrightarrow> (x, x) \<in> r" using \<open>r = s \<times> s\<close> by auto
  qed
  moreover have "sym r"
  proof
    fix x y
    assume "(x, y) \<in> r"
    then have "(x, y) \<in> s \<times> s" using \<open>r = s \<times> s\<close> by simp
    then have "x \<in> s" and "y \<in> s" by auto
    hence "(y, x) \<in> s \<times> s" by (simp add: SigmaI)
    thus "(y, x) \<in> r" using \<open>r = s \<times> s\<close> by simp
  qed
  moreover have "trans r"
  proof
    fix x y z
    assume "(x, y) \<in> r" and "(y, z) \<in> r"
    then have "x \<in> s" and "y \<in> s" and "z \<in> s" using \<open>r = s \<times> s\<close> by auto
    hence "(x, z) \<in> s \<times> s" by (simp add: SigmaI)
    thus "(x, z) \<in> r" using \<open>r = s \<times> s\<close> by simp
  qed
  ultimately show ?thesis
    unfolding equiv_def by simp
qed


fun R_right::"R \<Rightarrow> State \<Rightarrow> State list" where
"R_right [] s = []"|
"R_right (x#xs) s = (if fst x = s  then (snd x) # R_right xs s else  R_right xs s)" 

fun R_left::"R \<Rightarrow> State \<Rightarrow> State list" where
"R_left [] s = []"|
"R_left (x#xs) s = (if snd x = s  then (fst x) # R_left xs s else  R_left xs s)"
value"R_right R1 ''s2''"
value"R_right R1 ''s''"
value"R_right R1 ''s0''"
value "R_left R1 ''s1''"
value "R_left R1 ''t''"
value "R_left R1 ''s0''"

lemma R_right_empty:
  "R_right [] s = []"
  by simp
lemma R_left_empty:
  "R_left [] s = []"
  by simp
lemma R_right_subset:
  "set (R_right r s) \<subseteq> {t. (s, t) \<in> set r}"
  by (induct r s rule: R_right.induct) auto
lemma R_left_subset:
  "set (R_left r s) \<subseteq> {t. (t, s) \<in> set r}"
  by (induct r s rule: R_left.induct) auto
lemma R_right_empty_iff:
  "R_right r s = [] \<longleftrightarrow> (\<forall>t. (s, t) \<notin> set r)"
  by (induct r s rule: R_right.induct) auto
lemma R_left_empty_iff:
  "R_left r s = [] \<longleftrightarrow> (\<forall>t. (t, s) \<notin> set r)"
  by (induct r s rule: R_left.induct) auto
lemma R_right_correct: "(s, x) \<in> set r \<longleftrightarrow> x \<in> set (R_right r s)"  
  by (induct r s rule: R_right.induct) auto
lemma R_left_correct: "(x, s) \<in> set r \<longleftrightarrow> x \<in> set (R_left r s)"
  by (induct r s rule: R_left.induct) auto

lemma R_right_R_left: "t \<in> set (R_right r s) \<Longrightarrow> s \<in> set (R_left r t)"
  using R_left_correct R_right_correct by blast


(*
lemma R_right_symR:
  assumes "sym (set r)"
  shows "set (R_right r s1) = set (R_left r s1)"
proof -
  have "\<And>x. x \<in> set (R_right r s1) \<longleftrightarrow> x \<in> set (R_left r s1)"
  proof
    fix x assume "x \<in> set (R_right r s1)"
    then have "(s1, x) \<in> set r"
      using R_right_correct by blast
    moreover from assms have "(x, s1) \<in> set r"
      unfolding sym_def using calculation by auto
    hence "x \<in> set (R_left r s1)"
      using R_left_correct by blast
    thus "x \<in> set (R_left r s1)" .
  next fix x assume "x \<in> set (R_left r s1)"
    then have "(x, s1) \<in> set r" using R_left_correct by blast
    moreover from assms have "(s1, x) \<in> set r"
      unfolding sym_def using calculation by auto
    hence "x \<in> set (R_right r s1)"
      using R_right_correct by blast
    thus "x \<in> set (R_right r s1)" .
  qed
  thus ?thesis by auto
qed
*)

lemma R_right_symR:"sym (set r) \<Longrightarrow> set (R_right r s1) = set (R_left r s1)"
  apply (auto simp add :sym_def)
  apply (subgoal_tac"(s1,x)\<in>set r \<and> (x,s1)\<in> set r")
  using R_left_correct apply blast
  using R_right_correct apply blast
  using R_left_correct R_right_correct by blast





fun get_R_states::"R\<Rightarrow>State list" where
"get_R_states [] =[]"|
"get_R_states (a#xs) = ((fst a) # (snd a) # get_R_states xs)"

lemma get_R_states_empty:
  "get_R_states [] = []"
  by auto
lemma get_R_states_notempty:"s1\<in>set(get_R_states r) \<Longrightarrow> r\<noteq>[]"
  by auto

lemma get_R_states_cons:
  "get_R_states (xs@ys) = (get_R_states xs @ get_R_states ys)"
  apply (induct xs)
  apply simp
  by simp
  
lemma get_R_states_set:
  "set (get_R_states r) = {s. \<exists>t. (s, t) \<in> set r} \<union> {t. \<exists>s. (s, t) \<in> set r}"
  by (induct r rule:get_R_states.induct) auto
lemma get_R_states_subset:"set (get_R_states r) \<subseteq> set (get_R_states (a#r))"
  apply (induct r)
  apply simp 
  by auto 
lemma get_R_states_subempty:"set (get_R_states r1) \<subseteq> set (get_R_states []) \<Longrightarrow> r1 = [] "
  apply (induct r1)
  apply simp
  by auto

lemma get_R_states_delsubset:"set (get_R_states (a # r)) =  s \<Longrightarrow>  (s - {fst a} - {snd a}) \<subseteq> set (get_R_states r)"
  by auto

lemma get_R_states_setset:"set (get_R_states r)= \<Union>s \<Longrightarrow> \<forall>x\<in>s. card x = 1  \<Longrightarrow> x\<in>set (get_R_states r) \<longleftrightarrow> {x}\<in>s"
  by (metis Union_iff card_1_singletonE singleton_iff)

definition RL_check ::"R \<Rightarrow> Distr \<Rightarrow> Distr \<Rightarrow> bool" where
"RL_check r \<mu> \<nu> \<equiv> (\<forall>s1\<in> set(get_R_states r). 
                                ((get_value \<mu> s1) \<le> (get_values \<nu> (R_right r s1))) \<and> 
                                ((get_value \<nu> s1) \<le> (get_values \<mu> (R_left r s1))))"
definition RL_check_dl::"R  \<Rightarrow> Distr list \<Rightarrow> Distr list \<Rightarrow> bool" where
"RL_check_dl r d1 d2 \<equiv> d1\<noteq>[]\<and>d2\<noteq>[]\<and>(\<forall>\<mu>\<in>set d1.  \<exists>\<nu>\<in> set d2.  RL_check r \<mu> \<nu>)"

lemma RL_check_value_order:
  assumes "RL_check r \<mu> \<nu>"
  shows "\<forall>s1 \<in> set (get_R_states r). get_value \<mu> s1 \<le> get_values \<nu> (R_right r s1)"
        "\<forall>s1 \<in> set (get_R_states r). get_value \<nu> s1 \<le> get_values \<mu> (R_left r s1)"
  using RL_check_def assms apply auto[1]
  using RL_check_def assms by auto

lemma RL_check_dl_soundness_value_order:
  assumes "RL_check_dl r d1 d2"
  shows "\<forall>\<mu> \<in> set d1. \<exists>\<nu> \<in> set d2. RL_check r \<mu> \<nu> \<and> (\<forall>s1\<in>set (get_R_states r). get_value \<mu> s1 \<le> get_values \<nu> (R_right r s1)) 
                                                  \<and> (\<forall> s1 \<in> set (get_R_states r). get_value \<nu> s1 \<le> get_values \<mu> (R_left r s1))"
  by (meson RL_check_dl_def RL_check_value_order(1) RL_check_value_order(2) assms)

lemma RL_check_soundness:
  assumes "RL_check r \<mu> \<nu>" and "s1 \<in> set (get_R_states r)"
  shows "get_value \<mu> s1 \<le> get_values \<nu> (R_right r s1)" and "get_value \<nu> s1 \<le> get_values \<mu> (R_left r s1)"
  using RL_check_def assms(1) assms(2) apply auto[1]
  by (simp add: RL_check_value_order(2) assms(1) assms(2))
lemma RL_check_dl_soundness_complete:
  assumes "RL_check_dl r d1 d2" and "\<forall>\<mu>\<in>set d1. \<exists>\<nu>\<in>set d2. RL_check r \<mu> \<nu>"
  shows "\<forall>\<mu>\<in>set d1. \<exists>\<nu>\<in>set d2. RL_check r \<mu> \<nu> \<and> (\<forall>s1\<in>set (get_R_states r). get_value \<mu> s1 \<le> get_values \<nu> (R_right r s1)) 
                                              \<and>(\<forall>s1\<in>set (get_R_states r). get_value \<nu> s1 \<le> get_values \<mu> (R_left r s1))"
  using RL_check_dl_soundness_value_order assms(1) by blast

fun allact::"NFTS \<Rightarrow> Act list" where
"allact [] = []"|
"allact (x#xs)  = remdups ((fst (snd x))# allact xs)"
fun get_act::"(State \<times> State) \<Rightarrow>NFTS \<Rightarrow> Act list \<Rightarrow>Act list " where
"get_act (s0,t0) f [] = []"|
"get_act (s0,t0) f (a#xs) =(if (get_distr f s0 a)\<noteq>[] \<or> (get_distr f t0 a)\<noteq>[]
                            then a#get_act (s0,t0) f xs
                            else get_act (s0,t0) f xs )" 

lemma allact_non_empty:
  "f\<noteq>[] \<Longrightarrow> allact f \<noteq> []"
  by (induct f rule: allact.induct) auto
lemma get_act_empty:
  "acts = [] \<Longrightarrow> get_act (s0, t0) f acts = []"
  by simp
lemma get_act_non_empty:"a \<in> set acts \<Longrightarrow> get_distr f (fst r) a \<noteq> [] \<or> get_distr f (snd r) a \<noteq> [] \<Longrightarrow>get_act r f acts \<noteq> []"
  apply (induct r f acts  rule: get_act.induct)
  apply simp
  using get_act.elims list.discI list.inject prod.collapse set_ConsD by auto
lemma get_act_subset: "set (get_act x f acts) \<subseteq> set acts"
  apply (induct x f acts rule:get_act.induct) by auto

fun BIS_RL ::"R \<Rightarrow> R \<Rightarrow> NFTS \<Rightarrow>bool" where
"BIS_RL [] _ _  = True"|
"BIS_RL ((s0,t0)#xs) r f  = (
                           if
                              (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). RL_check_dl r (get_distr f s0 a1) (get_distr f t0 a1)) 
                           then True\<and>BIS_RL xs r f
                           else False)"

fun BIS::"R\<Rightarrow>R\<Rightarrow> NFTS \<Rightarrow>R" where
"BIS [] _ _  = []"|
"BIS ((s0,t0)#xs) r  f  = (
                           if
                              (\<forall>a1\<in>set(get_act (s0,t0) f (allact f)). RL_check_dl r (get_distr f s0 a1) (get_distr f t0 a1)) 
                           then (s0,t0)#BIS xs r f
                           else BIS xs r f
                          )"
lemma BIS_subset:"set (BIS r1 r2 f) \<subseteq> set r1"
  apply (induct r1 r2 f rule:BIS.induct) by auto

function BIS_induct ::"R\<Rightarrow>NFTS\<Rightarrow>R" where
"BIS_induct [] _ = []"|
"BIS_induct r f = (if(BIS r r f) = r then r else BIS_induct (BIS r r f) f)"
  by pat_completeness auto

lemma length_BIS:" length (BIS r r2 f) \<le> length r"
  apply (induct r arbitrary: r2 f)
  apply auto
  by (simp add: le_Suc_eq)
lemma length_BIS_uneq:"BIS r r2 f \<noteq> r \<Longrightarrow> length (BIS r r2 f) < length r"
  apply (induct r arbitrary: r2 f)
  apply auto
  by (metis less_Suc_eq)
termination
  apply (relation "measure (\<lambda>(r, f). length r)")
  apply auto
  apply (subgoal_tac "length (BIS r r f) \<noteq> length r")
  apply (simp add: length_BIS order_neq_le_trans)
  using length_BIS_uneq by force



export_code BIS BIS_induct in Haskell module_name Example

definition equivalence_R ::"NFTS \<Rightarrow> R"where
"equivalence_R f \<equiv>  BIS_induct (init_R_list (allstates_list f) (allstates_list f)) f"

end