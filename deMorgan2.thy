theory deMorgan2
  imports Main

begin
text\<open> Apply style \<close>
lemma conj_swap: "\<not> p \<and> \<not> q \<Longrightarrow> \<not> q \<and> \<not> p"
  apply (rule conjI)
   apply (drule conjunct2)
   apply (assumption)
  apply (drule conjunct1)
  apply (assumption)
  done

lemma dm_law_2: "(\<not>p \<and> \<not> q) \<longrightarrow> \<not>(p \<or> q)"
  apply (rule impI)
  apply (rule notI)
  apply (erule disjE)
   apply (erule conjE)
   apply (erule notE)
   apply (assumption)
  apply (drule conj_swap)
  apply (erule conjE)
  apply (erule notE)
  apply (assumption)
  done

end
