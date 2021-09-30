theory deMorgan3
  imports Main
begin

lemma deMorgan3: "(\<not>p \<or> \<not>q) \<longrightarrow> \<not>(p \<and> q)"
	apply (rule impI)
	apply (erule disjE)
	 apply (rule notI)
	 apply (erule notE)
	 apply (erule conjE)
	 apply assumption
	apply (rule notI)
	apply (erule notE)
	apply (erule conjE)
	apply assumption
	done
end