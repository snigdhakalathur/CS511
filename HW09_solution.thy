text\<open> 4 Nov 2021: Two lemmas for Homework 09 in CS 511 \<close> 

theory HW09_solution
  imports Main
begin

text \<open> Exercise 1 on the last page of Lecture Slides 28, Analytic Tableaux
       Part I  \<close>

lemma A1 : " (\<forall>x. \<forall>y. \<forall>z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<and> (\<forall>x. \<forall>y. P(x,y) \<longrightarrow> P(y,x)) 
            \<Longrightarrow> \<forall>x. \<forall>y. \<forall>z. P(x,y) \<and> P(z,y) \<longrightarrow> P(x,z) "
  by blast 

lemma A2 : " (\<forall>x. \<forall>y. \<forall>z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<and> (\<forall>x. \<forall>y. P(x,y) \<longrightarrow> P(y,x)) 
               \<Longrightarrow> \<forall>x. \<forall>y. \<forall>z. P(x,y) \<and> P(z,y) \<longrightarrow> P(x,z) "
  apply (erule conjE)
  apply (rule allI)+
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="z" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="z" in allE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply (rule conjI)
  apply assumption+
  done

text \<open> Exercise 2 on the last page of Lecture Slides 28, Analytic Tableaux
       Part I  \<close>
lemma B1: "\<forall>x. Q(a,x,x) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x) "
  by blast 

text \<open> A bloated proof of Lemma B1 with several unnecessary 'apply' steps \<close>
lemma B2: "(\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)
  apply (erule conjE)
  apply (rule_tac x="s(s(s(s(s(a)))))" in exI)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="a" in allE)
  apply (frule_tac x="a" in spec)
  apply (frule_tac x="s(a)" in spec)
  apply (frule_tac x="s(s(a))" in spec)
  apply (erule_tac x="a" in allE) 
  apply (frule_tac x="a" in spec)
  apply (frule_tac x="s(s(a))" in spec) 
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(s(a)))" in allE)
  apply (erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule_tac x="a" in allE)  
  apply (erule_tac x="a" in allE) 
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="a" in allE) 
  apply (erule impE)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply (erule mp)
  apply assumption
  done

text \<open> The following proof is essentially the same as that for B2 above, 
       the difference being that all explicit substitutions, except for one,
       are omitted. As a result, Isabelle will replace every quantified variable
       by a schematic variable, also trusting Isabelle's unification engine
       to figure out appropriate substitutions. \<close>
lemma B2_bis: "(\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)
  apply (erule conjE)
  apply (rule exI)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (frule_tac x="a" in spec)
  apply (frule spec)
  apply (frule spec)
  apply (frule spec)
  apply (erule allE)
  apply (frule spec) 
  apply (frule spec)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule impE)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply (erule mp)
  apply assumption
  done

text\<open> In the proofs to follow we use commands of the form: 'apply (rotate_tac n)'
      which rotates the premises of a subgoal by n positions, from RIGHT to LEFT
      if n is positive, and from LEFT to RIGHT if n is negative. \<close>

text \<open> Shortest proofs below are for Lemmas B3 and B4 \<close>

text \<open> A streamlined proof of Lemmas B1 and B2 with 12 'apply' steps \<close>
lemma B3: " (\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)+
  apply (rule_tac x="s(s(s(s(s(a)))))" in exI)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="a" in allE)
      (* rotate premises RIGHT to LEFT by 2 before applying rule 'allE' *)
  apply (rotate_tac 2, erule_tac x="s(s(a))" in allE)
      (* rotate premises RIGHT to LEFT by 2 before applying rule 'allE' *)
  apply (rotate_tac 2, erule_tac x="s(s(a))" in allE)
  apply (frule_tac x="a" in spec)
      (* rotate premises RIGHT to LEFT by 3 before applying rule 'allE' *)
  apply (rotate_tac 3, erule_tac x="s(s(a))" in allE)
  apply (frule_tac x="s(a)" in spec, rotate_tac 2, erule_tac x="s(s(s(a)))" in allE)
  apply (erule_tac x="s(s(a))" in allE, erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule impE, assumption)+
  by assumption

text \<open> A slight variation of the proof of Lemma B3 with 13 'apply' steps \<close>
lemma B4: " (\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)+
  apply (rule exI)
  apply (erule allE)
  apply (erule_tac x="s(s(a))" in allE) 
  apply (erule_tac x="a" in allE) 
      (* rotate premises LEFT to RIGHT by 1 before applying rule 'allE' *)
  apply (rotate_tac -1, erule_tac x="s(s(a))" in allE) 
      (* rotate premises LEFT to RIGHT by 1 before applying rule 'allE' *)
  apply (rotate_tac -1, erule_tac x="s(s(a))" in allE)
  apply (frule_tac x="a" in spec)
      (* rotate premises RIGHT to LEFT by 3 before applying rule 'allE' *)
  apply (rotate_tac 3, erule_tac x="s(s(a))" in allE)
  apply (frule_tac x="s(a)" in spec, rotate_tac 2, erule_tac x="s(s(s(a)))" in allE)
  apply (erule_tac x="s(s(a))" in allE, erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule impE, assumption)+
  apply assumption
  done

text \<open> The proofs of Lemmas B5 and B6 are obtained from the proof of B2 by 
       repeated trial-error-backtrack steps \<close>

text \<open> A shorter proof of Lemmas B1 and B2 with 19 'apply' steps, but still bloated \<close>
lemma B5: " (\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)+
  apply (rule_tac x="s(s(s(s(s(a)))))" in exI)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="a" in allE)
  apply (frule_tac x="a" in spec)
  apply (frule_tac x="s(a)" in spec)
  apply (erule_tac x="s(s(a))" in allE)  
  apply (frule_tac x="a" in spec)
  apply (erule_tac x="s(s(a))" in allE) 
  apply (erule_tac x="s(s(a))" in allE) 
  apply (erule_tac x="s(s(s(a)))" in allE)
  apply (erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule impE)
   apply (erule mp)
   apply assumption
  apply (erule mp)+
  by assumption

text \<open> A shorter proof of Lemmas B1 and B2 with 21 'apply' steps, but still bloated \<close>
lemma B6: " (\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)+
  apply (rule_tac x="s(s(s(s(s(a)))))" in exI)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (rotate_tac 2) 
  apply (frule_tac x="a" in spec)
  apply (frule_tac x="s(a)" in spec)
  apply (erule_tac x="s(s(a))" in allE)  
  apply (frule_tac x="a" in spec)
  apply (erule_tac x="s(s(a))" in allE) 
  apply (erule_tac x="s(s(a))" in allE) 
  apply (erule_tac x="s(s(s(a)))" in allE)
  apply (erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule impE)
   apply (rotate_tac 4)
   apply (erule_tac x="s(s(a))" in allE)
   apply (erule mp)
  apply assumption 
   apply (erule mp)
  apply (erule mp)
  by assumption

end