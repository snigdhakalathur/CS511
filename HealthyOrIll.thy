theory HealthyOrIll
  imports Main

begin

lemma hoi: "(healthy \<or> ill) \<and> (healthy \<longrightarrow> travel) \<and> \<not>ill \<longrightarrow> travel"
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule impE)
   apply (erule disjE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule disjE)
   apply assumption
  apply assumption
  done
end