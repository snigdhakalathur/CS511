text\<open> 1 October 2021: Exercise for Homework Assignment 05 in CS 511 \<close> 
text\<open> Your task to remove every invocation of the pre-defined method blast,
      by an equivalent sequence of 'apply' steps \<close>

theory HW05
  imports Main
begin

lemma prelim1 : "(True \<longrightarrow> A) \<Longrightarrow> A"
  apply(erule impE)
   apply(rule TrueI)
  apply assumption
  done

lemma prelim2 : "((Phi = False) \<and> Psi1 \<and> Psi2) \<or> (Phi = True) \<Longrightarrow> (Phi \<or> Psi1) \<and> (Phi \<or> Psi2)"
   apply (erule disjE)
    apply (erule conjE)+
    apply (rule conjI)
     apply (rule disjI2)
     apply assumption
    apply (rule disjI2)
    apply assumption
   apply (rule conjI)
    apply (rule disjI1)
    apply (erule iffE)
    apply (erule impE)
     apply (rule prelim1)
     apply assumption
    apply (erule mp)
    apply assumption
   apply (erule iffE)
   apply (erule impE)
    apply (rule prelim1)
    apply assumption
   apply (rule disjI1)
   apply (erule mp)
  apply assumption
  done

lemma prelim3 : "(Phi \<or> Psi1) \<and> (Phi \<or> Psi2) \<Longrightarrow> ((Phi = False) \<and> Psi1 \<and> Psi2) \<or> (Phi = True)"
  apply (erule conjE)
  apply (erule disjE)+
    apply (rule disjI2)
    apply (rule iffI)
     apply (rule TrueI)
    apply assumption
   apply (rule disjI2)
   apply (rule iffI)
    apply (rule TrueI)
   apply assumption
  apply(erule disjE)
   apply (rule disjI2)
   apply (rule iffI)
    apply (rule TrueI)
   apply assumption
  apply clarify
  apply (rule conjI)
   apply (rule iffI)
    apply (erule notE)
    apply (rule iffI)
    apply (rule TrueI)
    apply assumption
    apply (erule notE)
   apply (rule iffI)
    apply (rule TrueI)
   apply (rule classical)
   apply (rule FalseE)
   apply assumption  
  apply (rule conjI)
  apply (rule classical)
   apply (rule FalseE)
   apply (erule notE)
   apply (rule iffI)
    apply (rule TrueI)
  apply (rule classical)
   apply (rule FalseE)
  apply (erule notE)
   apply assumption
  apply (rule classical)
   apply (rule FalseE)
  apply (erule notE)
  apply (rule iffI)
   apply (rule TrueI)
  apply (rule classical)
  apply (rule FalseE)
  apply (erule notE)
  apply assumption
  done

theorem "((Phi = False) \<and> Psi1 \<and> Psi2) \<or> (Phi = True) \<longleftrightarrow> (Phi \<or> Psi1) \<and> (Phi \<or> Psi2)"
  apply (rule iffI)
   apply (erule prelim2)
  apply (erule prelim3)
  done

end