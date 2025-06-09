theory NFTS
  imports Complex_Main
begin

type_synonym Act ="char list"
type_synonym State ="char list"
type_synonym Distr = "(real \<times> State) list"
type_synonym Transition = "(State \<times> Act \<times> Distr)"
type_synonym NFTS = "(State \<times> Act \<times> Distr) list"

definition "distr1::Distr \<equiv> [(0.4,''s2''),(0.7,''s3''),(0.5,''s4'')]"
definition "distr2::Distr \<equiv> [(0.5,''s2''),(0.6,''s3''),(0.7,''s4''),(0.8 ,''s5'')]"
definition "NFTS1::NFTS \<equiv> [(''s'',''a'',distr1),(''t'',''a'',distr2)]"
definition "transition1 \<equiv> (''s'',''a'',distr1)"
value"NFTS1"


fun alldistr ::"NFTS \<Rightarrow> Distr list" where
"alldistr [] = []"|
"alldistr (x#xs) = snd(snd x) # alldistr xs"
value"alldistr NFTS1"


definition get_a_distr::"Transition \<Rightarrow> State \<Rightarrow> Act \<Rightarrow> Distr"where
"get_a_distr t s a \<equiv> if(fst t) = s \<and> (fst (snd t) = a) then snd (snd t) else []"
value"get_a_distr transition1 ''s'' ''a''"
value"get_a_distr transition1 ''s2'' ''a''"
value"get_a_distr transition1 ''s'' ''b''"


fun get_distr::"NFTS \<Rightarrow> State \<Rightarrow> Act \<Rightarrow> Distr list"where
"get_distr [] s a = []"|
"get_distr (x#xs) s a = (if(get_a_distr x s a \<noteq> []) then (get_a_distr x s a)# get_distr xs s a  else get_distr xs s a)"
value"get_distr NFTS1 ''s'' ''a''"
value"get_distr NFTS1 ''t'' ''b''"
value"get_distr NFTS1 ''s'' ''b''"
value"get_distr [(''s'',''a'',[(0.7,''s1''),(0.6,''s2''),(0.7,''s3'')]),
                         (''s'',''a'',[(0.7,''s1''),(0.5,''s2''),(0.7,''s3'')])] ''s'' ''a''"


fun get_value::"Distr \<Rightarrow> State  \<Rightarrow> real" where
"get_value [] _ = 0 "|
"get_value (x#xs) s = (if (snd x) = s then (fst x) else (get_value xs s))"
value "get_value distr1 ''s3''"
value "get_value distr1 ''s''"


fun get_values::"Distr \<Rightarrow> State list  \<Rightarrow> real" where
"get_values [] _ = 0"|
"get_values \<mu> [] = 0"|
"get_values \<mu> (y#ys) = max (get_value \<mu> y) (get_values \<mu> ys)"
value"get_values distr1 [''s2'',''s3'',''s4'',''s'']" 

definition get_values_set::"Distr \<Rightarrow> State set  \<Rightarrow> real" where
"get_values_set \<mu> S \<equiv> if S={} then 0 else Max ((image (get_value \<mu>) S ) \<union> {0})"
value"get_values_set distr1 {''s2'',''s3'',''s4'',''s''}"

lemma get_values_set_range:"finite S\<Longrightarrow>get_values_set \<mu> S \<ge> 0"
  by (simp add: get_values_set_def)
lemma get_values_set_Dempty:"get_values_set [] S = 0 "
  by (simp add: get_values_set_def image_constant_conv)
lemma get_values_set_Sempty:"get_values_set \<mu> {} = 0 "
  by (simp add: get_values_set_def)
lemma get_values_set_Max:"finite B \<Longrightarrow> \<forall>s1\<in>B. get_value \<nu> s1 \<le> 0 \<Longrightarrow> get_values_set \<nu> B = 0"
  by (simp add: get_values_set_def )
 

fun get_states ::"Distr \<Rightarrow> State list" where
"get_states [] =[]"|
"get_states (x#xs) = (snd x)#(get_states xs)"
value"get_states distr1"

fun get_states_dl ::"Distr list\<Rightarrow> State list" where
"get_states_dl [] =[]"|
"get_states_dl (x#xs) = (get_states x)@(get_states_dl xs)"


definition get_states_tran ::"Transition \<Rightarrow>State \<Rightarrow>Act \<Rightarrow> State list" where
" get_states_tran t s a \<equiv>if(fst t) = s \<and> (fst (snd t) = a) then get_states (snd (snd t))  else []"
value"get_states_tran transition1 ''s'' ''a''"
value"get_states_tran transition1 ''s'' ''b''"


definition get_states_NFTS ::"NFTS \<Rightarrow> State \<Rightarrow> Act \<Rightarrow> State list" where
"get_states_NFTS f s a \<equiv> get_states_dl (get_distr f s a)"
value"get_states_NFTS NFTS1 ''s'' ''a''"
value"get_states_NFTS NFTS1 ''t'' ''b''"
value"get_states_NFTS NFTS1 ''s2'' ''b''"
value"get_states_NFTS [(''s'',''a'',[(0.7,''s1''),(0.6,''s2''),(0.7,''s3'')]),
                         (''s'',''a'',[(0.7,''s1''),(0.5,''s2''),(0.7,''s3'')])] ''s'' ''a''"


definition inclusion::"Transition \<Rightarrow> State \<Rightarrow> Distr" where
"inclusion t s \<equiv> (if(s\<in>set(get_states(snd (snd t)))) then (snd (snd t)) else [])"
value"inclusion transition1 ''s1''" 
value"inclusion transition1 ''s2''" 


fun inclusions ::"NFTS \<Rightarrow> State \<Rightarrow> Distr list" where
"inclusions [] _ = []"|
"inclusions (x#xs) s = (if (inclusion x s \<noteq> []) then ((snd (snd x))#inclusions xs s) else inclusions xs s)"
value "inclusions NFTS1 ''s0'' "
value "inclusions NFTS1 ''s2'' "


fun pre ::"NFTS \<Rightarrow> State  \<Rightarrow> State list" where
"pre [] _ = []"|
"pre (x#xs) s = (if (snd (snd x)) = (inclusion x s) then ( (fst x)#pre xs s) else pre xs s )"
value"pre  NFTS1 ''s2'' "
value"pre  NFTS1 ''s5'' "
value"pre  NFTS1 ''s0'' "


fun allstates::"NFTS \<Rightarrow> State set" where
"allstates [] = {}"|
"allstates (x#xs) = {fst x} \<union> set (get_states (snd (snd x))) \<union> allstates xs"
value"allstates NFTS1"
value"allstates []"

fun allstates_list::"NFTS \<Rightarrow> State list" where
"allstates_list [] = []"|
"allstates_list (x#xs) = (fst x # (get_states (snd (snd x))) @ allstates_list xs)"

lemma allstates_nonempty:"f\<noteq>[] \<Longrightarrow>(allstates f)\<noteq>{} "
  by (induct f) auto
lemma allstates_list_nonempty:"f\<noteq>[] \<Longrightarrow>(allstates_list f)\<noteq>[] "
  by (induct f) auto

lemma get_distr_inNFTS:" set (get_distr f s a) \<subseteq> set(alldistr f)"
  apply (induct f s a rule: get_distr.induct )
  by(auto simp add: get_a_distr_def)

lemma get_states_inNFTS:" set (get_states_NFTS f s a)  \<subseteq> allstates f "
  apply (simp add: get_states_NFTS_def)
  apply (induct f s a rule:get_distr.induct)
  apply simp
  apply (auto simp add:get_a_distr_def)
  done

lemma get_value_inDistr:"get_value \<mu> s =v \<and> v \<noteq>0 \<Longrightarrow>  s\<in> set(get_states \<mu>)"
  apply (induct \<mu> rule:get_states.induct)
  apply simp
  by fastforce

theorem get_values_inDIStr:"get_values \<mu> s =v \<and> v\<noteq>0 \<Longrightarrow> get_value \<mu> s1 = v \<Longrightarrow> s1\<in> set(get_states \<mu>) "
proof -
  assume a1: "get_value \<mu> s1 = v"
  assume "get_values \<mu> s = v \<and> v \<noteq> 0"
  then have "0 \<noteq> get_value \<mu> s1"
    using a1 by metis
  then show ?thesis
    by (metis get_value_inDistr)
qed

lemma subset_inclusions:"set (inclusions \<mu> s) \<subseteq> set (alldistr \<mu>)"
  apply (induct  \<mu> rule: alldistr.induct)
  apply simp
  apply (simp add:inclusion_def)
  by auto

lemma subset_pre:"set (pre \<mu> s) \<subseteq> allstates \<mu>"
  apply (induct \<mu> s  rule: pre.induct)
  apply simp
  apply (simp add:inclusion_def)
  by auto

end