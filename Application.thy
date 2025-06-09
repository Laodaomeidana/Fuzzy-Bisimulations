theory Application
  imports Bisimulation Bis_R_closed Complex_Main R_closed_algorithm
begin

type_synonym FRDF = "NFTS"
type_synonym FPN = "NFTS"

definition "f1::NFTS \<equiv> [(''s'',''a'',[(0.7,''s1''),(0.6,''s2'')]),
                        (''s'',''a'',[(0.6,''s3''),(0.8,''s4'')]),
                        (''s2'',''b'',[(0.5,''s5''),(0.7,''s6'')])]"

definition "f2::NFTS \<equiv> [(''t'',''a'',[(0.7,''t1''),(0.6,''t2''),(0.4,''t3'')]),
                        (''t'',''a'',[(0.5,''t4''),(0.9,''t5'')]),
                        (''t2'',''b'',[(0.7,''t6''),(0.2,''t7'')]),
                        (''t5'',''c'',[(0.8,''t8'')])]"

definition "f::NFTS \<equiv> [(''s'',''a'',[(0.7,''s1''),(0.6,''s2'')]),
                        (''s'',''a'',[(0.6,''s3''),(0.8,''s4'')]),
                        (''s2'',''b'',[(0.5,''s5''),(0.7,''s6'')]),
                        (''t'',''a'',[(0.7,''t1''),(0.6,''t2''),(0.4,''t3'')]),
                        (''t'',''a'',[(0.5,''t4''),(0.9,''t5'')]),
                        (''t2'',''b'',[(0.7,''t6''),(0.2,''t7'')]),
                        (''t5'',''c'',[(0.8,''t8'')])]"

value "{''s'',''s1'',''s2'',''s3'',''s4'',''s5'',''s6''} \<times> {''t'',''t1'',''t2'',''t3'',''t4'',''t5'',''t6'',''t7'',''t8''}"
definition "rs::R \<equiv>
 [(''s'', ''t''), (''s'', ''t1''), (''s'', ''t2''), (''s'', ''t3''), (''s'', ''t4''), (''s'', ''t5''), (''s'', ''t6''),
  (''s'', ''t7''), (''s'', ''t8''), (''s1'', ''t''), (''s1'', ''t1''), (''s1'', ''t2''), (''s1'', ''t3''), (''s1'', ''t4''),
  (''s1'', ''t5''), (''s1'', ''t6''), (''s1'', ''t7''), (''s1'', ''t8''), (''s2'', ''t''), (''s2'', ''t1''), (''s2'', ''t2''),
  (''s2'', ''t3''), (''s2'', ''t4''), (''s2'', ''t5''), (''s2'', ''t6''), (''s2'', ''t7''), (''s2'', ''t8''), (''s3'', ''t''),
  (''s3'', ''t1''), (''s3'', ''t2''), (''s3'', ''t3''), (''s3'', ''t4''), (''s3'', ''t5''), (''s3'', ''t6''), (''s3'', ''t7''),
  (''s3'', ''t8''), (''s4'', ''t''), (''s4'', ''t1''), (''s4'', ''t2''), (''s4'', ''t3''), (''s4'', ''t4''), (''s4'', ''t5''),
  (''s4'', ''t6''), (''s4'', ''t7''), (''s4'', ''t8''), (''s5'', ''t''), (''s5'', ''t1''), (''s5'', ''t2''), (''s5'', ''t3''),
  (''s5'', ''t4''), (''s5'', ''t5''), (''s5'', ''t6''), (''s5'', ''t7''), (''s5'', ''t8''), (''s6'', ''t''), (''s6'', ''t1''),
  (''s6'', ''t2''), (''s6'', ''t3''), (''s6'', ''t4''), (''s6'', ''t5''), (''s6'', ''t6''), (''s6'', ''t7''), (''s6'', ''t8'')]"

definition "r::R\<equiv>[(''s2'', ''t2''), (''s1'', ''t1''), (''s1'', ''t3''), (''s1'', ''t4''), (''s1'', ''t6''), 
  (''s1'', ''t7''), (''s1'', ''t8''), (''s3'', ''t1''), (''s3'', ''t3''), (''s3'', ''t4''), (''s3'', ''t6''), 
  (''s3'', ''t7''), (''s3'', ''t8''), (''s4'', ''t1''), (''s4'', ''t3''), (''s4'', ''t4''), (''s4'', ''t6''), 
  (''s4'', ''t7''), (''s4'', ''t8''), (''s5'', ''t1''), (''s5'', ''t3''), (''s5'', ''t4''), (''s5'', ''t6''), 
  (''s5'', ''t7''), (''s5'', ''t8''), (''s6'', ''t1''), (''s6'', ''t3''), (''s6'', ''t4''), (''s6'', ''t6''), 
  (''s6'', ''t7''), (''s6'', ''t8'')]"

value "BIS_induct rs f"

value"get_distr f1 ''s'' ''a''"

value"allstates f1"

value "R_closed_set r f"

value "BIS_R_closed r r f"

value "BIS_RL r r f"


definition FRDF_Ex::"FRDF"where
"FRDF_Ex \<equiv> [(''URL'',''creator'',[(0.7,''p1''),(0.4,''p2'')]),
            (''p1'',''email'',[(0.7,''Jerry@gmail.com''),(0.5,''Jerry@yahoo.com'')]),
            (''p1'',''age'',[(0.5,''19''),(0.3,''23''),(0.9,''20'')]),
            (''p1'',''name'',[(0.6,''jerry'')]),
            (''p2'',''email'',[(0.6,''Tom@gmail.com''),(0.5,''Tom@yahoo.com'')]),
            (''p2'',''age'',[(0.8,''24''),(0.1,''32''),(0.7,''27'')]),
            (''p2'',''name'',[(0.3,''Tom'')])]"

definition "R_FRDF::R\<equiv>[(''URL'', ''URL''), (''URL'', ''Jerry@yahoo.com''), (''URL'', ''Jerry@gmail.com''), (''URL'', ''20''), (''URL'', ''23''),
  (''URL'', ''19''), (''URL'', ''jerry''), (''URL'', ''p1''), (''URL'', ''Tom@yahoo.com''), (''URL'', ''Tom@gmail.com''),
  (''URL'', ''27''), (''URL'', ''32''), (''URL'', ''24''), (''URL'', ''Tom''), (''URL'', ''p2''),
  (''Jerry@yahoo.com'', ''URL''), (''Jerry@yahoo.com'', ''Jerry@yahoo.com''), (''Jerry@yahoo.com'', ''Jerry@gmail.com''),
  (''Jerry@yahoo.com'', ''20''), (''Jerry@yahoo.com'', ''23''), (''Jerry@yahoo.com'', ''19''),
  (''Jerry@yahoo.com'', ''jerry''), (''Jerry@yahoo.com'', ''p1''), (''Jerry@yahoo.com'', ''Tom@yahoo.com''),
  (''Jerry@yahoo.com'', ''Tom@gmail.com''), (''Jerry@yahoo.com'', ''27''), (''Jerry@yahoo.com'', ''32''),
  (''Jerry@yahoo.com'', ''24''), (''Jerry@yahoo.com'', ''Tom''), (''Jerry@yahoo.com'', ''p2''),
  (''Jerry@gmail.com'', ''URL''), (''Jerry@gmail.com'', ''Jerry@yahoo.com''), (''Jerry@gmail.com'', ''Jerry@gmail.com''),
  (''Jerry@gmail.com'', ''20''), (''Jerry@gmail.com'', ''23''), (''Jerry@gmail.com'', ''19''),
  (''Jerry@gmail.com'', ''jerry''), (''Jerry@gmail.com'', ''p1''), (''Jerry@gmail.com'', ''Tom@yahoo.com''),
  (''Jerry@gmail.com'', ''Tom@gmail.com''), (''Jerry@gmail.com'', ''27''), (''Jerry@gmail.com'', ''32''),
  (''Jerry@gmail.com'', ''24''), (''Jerry@gmail.com'', ''Tom''), (''Jerry@gmail.com'', ''p2''), (''20'', ''URL''),
  (''20'', ''Jerry@yahoo.com''), (''20'', ''Jerry@gmail.com''), (''20'', ''20''), (''20'', ''23''), (''20'', ''19''),
  (''20'', ''jerry''), (''20'', ''p1''), (''20'', ''Tom@yahoo.com''), (''20'', ''Tom@gmail.com''), (''20'', ''27''),
  (''20'', ''32''), (''20'', ''24''), (''20'', ''Tom''), (''20'', ''p2''), (''23'', ''URL''), (''23'', ''Jerry@yahoo.com''),
  (''23'', ''Jerry@gmail.com''), (''23'', ''20''), (''23'', ''23''), (''23'', ''19''), (''23'', ''jerry''), (''23'', ''p1''),
  (''23'', ''Tom@yahoo.com''), (''23'', ''Tom@gmail.com''), (''23'', ''27''), (''23'', ''32''), (''23'', ''24''),
  (''23'', ''Tom''), (''23'', ''p2''), (''19'', ''URL''), (''19'', ''Jerry@yahoo.com''), (''19'', ''Jerry@gmail.com''),
  (''19'', ''20''), (''19'', ''23''), (''19'', ''19''), (''19'', ''jerry''), (''19'', ''p1''), (''19'', ''Tom@yahoo.com''),
  (''19'', ''Tom@gmail.com''), (''19'', ''27''), (''19'', ''32''), (''19'', ''24''), (''19'', ''Tom''), (''19'', ''p2''),
  (''jerry'', ''URL''), (''jerry'', ''Jerry@yahoo.com''), (''jerry'', ''Jerry@gmail.com''), (''jerry'', ''20''),
  (''jerry'', ''23''), (''jerry'', ''19''), (''jerry'', ''jerry''), (''jerry'', ''p1''), (''jerry'', ''Tom@yahoo.com''),
  (''jerry'', ''Tom@gmail.com''), (''jerry'', ''27''), (''jerry'', ''32''), (''jerry'', ''24''), (''jerry'', ''Tom''),
  (''jerry'', ''p2''), (''p1'', ''URL''), (''p1'', ''Jerry@yahoo.com''), (''p1'', ''Jerry@gmail.com''), (''p1'', ''20''),
  (''p1'', ''23''), (''p1'', ''19''), (''p1'', ''jerry''), (''p1'', ''p1''), (''p1'', ''Tom@yahoo.com''),
  (''p1'', ''Tom@gmail.com''), (''p1'', ''27''), (''p1'', ''32''), (''p1'', ''24''), (''p1'', ''Tom''), (''p1'', ''p2''),
  (''Tom@yahoo.com'', ''URL''), (''Tom@yahoo.com'', ''Jerry@yahoo.com''), (''Tom@yahoo.com'', ''Jerry@gmail.com''),
  (''Tom@yahoo.com'', ''20''), (''Tom@yahoo.com'', ''23''), (''Tom@yahoo.com'', ''19''), (''Tom@yahoo.com'', ''jerry''),
  (''Tom@yahoo.com'', ''p1''), (''Tom@yahoo.com'', ''Tom@yahoo.com''), (''Tom@yahoo.com'', ''Tom@gmail.com''),
  (''Tom@yahoo.com'', ''27''), (''Tom@yahoo.com'', ''32''), (''Tom@yahoo.com'', ''24''), (''Tom@yahoo.com'', ''Tom''),
  (''Tom@yahoo.com'', ''p2''), (''Tom@gmail.com'', ''URL''), (''Tom@gmail.com'', ''Jerry@yahoo.com''),
  (''Tom@gmail.com'', ''Jerry@gmail.com''), (''Tom@gmail.com'', ''20''), (''Tom@gmail.com'', ''23''),
  (''Tom@gmail.com'', ''19''), (''Tom@gmail.com'', ''jerry''), (''Tom@gmail.com'', ''p1''),
  (''Tom@gmail.com'', ''Tom@yahoo.com''), (''Tom@gmail.com'', ''Tom@gmail.com''), (''Tom@gmail.com'', ''27''),
  (''Tom@gmail.com'', ''32''), (''Tom@gmail.com'', ''24''), (''Tom@gmail.com'', ''Tom''), (''Tom@gmail.com'', ''p2''),
  (''27'', ''URL''), (''27'', ''Jerry@yahoo.com''), (''27'', ''Jerry@gmail.com''), (''27'', ''20''), (''27'', ''23''),
  (''27'', ''19''), (''27'', ''jerry''), (''27'', ''p1''), (''27'', ''Tom@yahoo.com''), (''27'', ''Tom@gmail.com''),
  (''27'', ''27''), (''27'', ''32''), (''27'', ''24''), (''27'', ''Tom''), (''27'', ''p2''), (''32'', ''URL''),
  (''32'', ''Jerry@yahoo.com''), (''32'', ''Jerry@gmail.com''), (''32'', ''20''), (''32'', ''23''), (''32'', ''19''),
  (''32'', ''jerry''), (''32'', ''p1''), (''32'', ''Tom@yahoo.com''), (''32'', ''Tom@gmail.com''), (''32'', ''27''),
  (''32'', ''32''), (''32'', ''24''), (''32'', ''Tom''), (''32'', ''p2''), (''24'', ''URL''), (''24'', ''Jerry@yahoo.com''),
  (''24'', ''Jerry@gmail.com''), (''24'', ''20''), (''24'', ''23''), (''24'', ''19''), (''24'', ''jerry''), (''24'', ''p1''),
  (''24'', ''Tom@yahoo.com''), (''24'', ''Tom@gmail.com''), (''24'', ''27''), (''24'', ''32''), (''24'', ''24''),
  (''24'', ''Tom''), (''24'', ''p2''), (''Tom'', ''URL''), (''Tom'', ''Jerry@yahoo.com''), (''Tom'', ''Jerry@gmail.com''),
  (''Tom'', ''20''), (''Tom'', ''23''), (''Tom'', ''19''), (''Tom'', ''jerry''), (''Tom'', ''p1''),
  (''Tom'', ''Tom@yahoo.com''), (''Tom'', ''Tom@gmail.com''), (''Tom'', ''27''), (''Tom'', ''32''), (''Tom'', ''24''),
  (''Tom'', ''Tom''), (''Tom'', ''p2''), (''p2'', ''URL''), (''p2'', ''Jerry@yahoo.com''), (''p2'', ''Jerry@gmail.com''),
  (''p2'', ''20''), (''p2'', ''23''), (''p2'', ''19''), (''p2'', ''jerry''), (''p2'', ''p1''), (''p2'', ''Tom@yahoo.com''),
  (''p2'', ''Tom@gmail.com''), (''p2'', ''27''), (''p2'', ''32''), (''p2'', ''24''), (''p2'', ''Tom''), (''p2'', ''p2'')]"

value "R_closed_set (BIS_induct R_FRDF FRDF_Ex) FRDF_Ex"


definition FPN_Ex::"FPN"where
"FPN_Ex \<equiv> [(''p1'',''t1'',[(0.9,''p3''),(0.2,''p4'')]),
            (''p1'',''t2'',[(0.1,''p3''),(0.9,''p4''),(0.1,''p5'')]),
            (''p1'',''t3'',[(0.2,''p4''),(0.9,''p5'')]),
            (''p2'',''t1'',[(0.9,''p3''),(0.2,''p4'')]),
            (''p2'',''t2'',[(0.1,''p3''),(0.9,''p4''),(0.1,''p5'')]),
            (''p2'',''t3'',[(0.2,''p4''),(0.9,''p5'')])]"

definition "R_FPN::R\<equiv>[(''p1'', ''p1''), (''p1'', ''p3''), (''p1'', ''p5''), (''p1'', ''p4''), (''p1'', ''p2''), (''p3'', ''p1''),
  (''p3'', ''p3''), (''p3'', ''p5''), (''p3'', ''p4''), (''p3'', ''p2''), (''p5'', ''p1''), (''p5'', ''p3''),
  (''p5'', ''p5''), (''p5'', ''p4''), (''p5'', ''p2''), (''p4'', ''p1''), (''p4'', ''p3''), (''p4'', ''p5''),
  (''p4'', ''p4''), (''p4'', ''p2''), (''p2'', ''p1''), (''p2'', ''p3''), (''p2'', ''p5''), (''p2'', ''p4''),
  (''p2'', ''p2'')]"

value "R_closed_set (BIS_induct R_FPN FPN_Ex) FPN_Ex"

end