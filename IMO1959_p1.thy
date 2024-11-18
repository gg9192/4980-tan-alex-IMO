theory IMO1959_p1
  imports "HOL-Computational_Algebra.Euclidean_Algorithm"
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

lemma IMO1959_p1:
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

end