theory IMO1959_p1
  imports "HOL-Computational_Algebra.Euclidean_Algorithm" "HOL.Rat"
begin         

section "helper lemmas"

lemma frac_gcd:
  (* this shows that the greatest common divisor between a and a*2 + 1 is 1*)
  fixes a b :: nat
  shows "(gcd a (2 * a + 1)) = 1"
  by (metis gcd_1_nat gcd_add_mult)

lemma euclidian_one_step:
  (* this does one iteration of the euclidian algorithm*)
  fixes a b :: nat
  assumes "a > b"
  shows "gcd (a) (b) = gcd (a-b) (b)"
  by (simp add: assms gcd_diff1_nat order_less_imp_le)

section "proof for the problem"

lemma gcd_1:
  (* this formalizes the problem using gcd rather than fractions*)
  fixes n::nat
  shows "gcd (21 * n + 4) (14 * n + 3) = 1"
proof -
  have gt: "(21 * n + 4) > (14 * n + 3)"
    by auto
  have onestep: "gcd (21 * n + 4) (14 * n + 3) = gcd (7 * n + 1) (14 * n + 3)"
    using euclidian_one_step[of "14 * n + 3" "21 * n + 4"] gt 
    by fastforce
  have gcd1: "gcd (7 * n + 1) (14 * n + 3) = 1"
    using  frac_gcd
    by (smt (verit) add.assoc add_mult_distrib2 mult.commute mult.left_commute numeral_Bit0_eq_double numeral_Bit1_eq_inc_double numerals(1))
  show ?thesis using gt gcd1
    using onestep by presburger
qed

lemma cant_simp:
  (* shows that if the gdc of the numerator and denominator are coprime, then the fraction can't be further simplified *)
  fixes a b::nat
  fixes f:: rat
  assumes "gcd a b = 1"
  assumes "f = (rat_of_nat a)/(rat_of_nat b)"
  shows "\<not>(\<exists> c d::nat. c < a \<and> d < b \<and> ((rat_of_nat c)/rat_of_nat d) = f)"
  using assms
proof - 
  have "\<exists> c d::nat. c < a \<and> d < b \<and> ((rat_of_nat c)/(rat_of_nat d)) = f \<Longrightarrow> False"
  proof - 
    assume "\<exists> c d::nat. c < a \<and> d < b \<and> ((rat_of_nat c)/(rat_of_nat d)) = f" 
    then obtain c d where cd: "c < a \<and> d < b \<and> ((rat_of_nat c)/(rat_of_nat d)) = f"
      by blast
    then have a: "a * d = c * b"
      by (metis (no_types, lifting) assms(2) divide_eq_0_iff frac_eq_eq less_imp_of_nat_less of_nat_eq_iff of_nat_less_0_iff of_nat_mult)
    have "coprime a b"
      using assms(1) by blast
    then have "a dvd c \<and> b dvd d" using a
      by (metis coprime_commute coprime_dvd_mult_right_iff dvd_triv_right mult.commute)
    then show "False"
      using cd assms(2) by fastforce
  qed
  then show ?thesis by auto 
qed

section "proof for the problem"

lemma IMO_1959_P1:
  fixes n::nat
  fixes f::rat
  assumes "f = (rat_of_nat (21 * n + 4)) / (rat_of_nat (14 * n + 3))"
  shows "\<not>(\<exists> c d::nat. c < (21 * n + 4) \<and> d < (14 * n + 3) \<and> ((rat_of_nat c)/(rat_of_nat d)) = f)"
  using assms
proof -
  show ?thesis using gcd_1 cant_simp
    using assms by presburger
qed
end