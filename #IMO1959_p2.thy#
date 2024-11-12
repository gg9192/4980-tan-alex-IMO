theory IMO1959_p2
  imports "HOL-Computational_Algebra.Euclidean_Algorithm" "HOL.Real"  "HOL.NthRoot"
begin         

lemma sqrt_abs:
  fixes x::real
  shows "sqrt (x^2) = abs x"
  using real_sqrt_abs by blast

lemma eq_simp:
  fixes x::real
  assumes "sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = A"
  assumes "2 * x - 1 \<ge> 0"
  assumes "x - sqrt (2 * x - 1) \<ge> 0"
  shows "A^2 = 2 * (x + abs(x - 1))"
  using assms
proof - 
  have a1: "(sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)))^2 = A^2" using assms
    by presburger
  then have "(x + sqrt(2*x - 1)) + 2*(sqrt (x + sqrt (2 * x - 1)))*(sqrt (x - sqrt (2 * x - 1))) + (x - sqrt(2*x - 1)) = (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)))^2"
  proof - 
    have a1: "(sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)))^2 = (sqrt (x + sqrt (2 * x - 1)))^2 + 2 * sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) + (sqrt (x - sqrt (2 * x - 1)))^2"
      by (simp add: power2_sum)
    then have a2: "(sqrt (x + sqrt (2 * x - 1)))^2 + 2 * sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) + (sqrt (x - sqrt (2 * x - 1)))^2 = 
    x + sqrt (2 * x - 1) + 2 * sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) +  (x - sqrt (2 * x - 1))" using assms
      by auto 
    then have a3: "x + sqrt (2 * x - 1) + 2 * sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) +  (x - sqrt (2 * x - 1)) = 
    x + sqrt (2 * x - 1) + 2 * sqrt ((x + sqrt (2 * x - 1))*(x - sqrt (2 * x - 1))) +  (x - sqrt (2 * x - 1))"
      by (simp add: mult.commute mult.left_commute real_sqrt_mult)
    show ?thesis using a1 a2 a3
      by presburger
  qed
  then have "(x + sqrt(2*x - 1)) + 2*(sqrt (x + sqrt (2 * x - 1)))*(sqrt (x - sqrt (2 * x - 1))) + (x - sqrt(2*x - 1)) = A^2"
    using a1
    by presburger
  then have "2 * x + 2*(sqrt (x + sqrt (2 * x - 1)))*(sqrt (x - sqrt (2 * x - 1))) = A^2"
    by auto
  then have "2 * x + 2*(sqrt ((x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1)))) = A^2"
    by (simp add: real_sqrt_mult)
  then have "2 * x + 2*(sqrt (x ^ 2 - (2 * x - 1))) = A^2"
    by (metis assms(2) power2_eq_square real_sqrt_pow2_iff square_diff_square_factored)
  then have "2 * x + 2*(sqrt (x ^ 2 - 2 * x + 1)) = A^2"
    by argo
  then have "2 * x + 2*(sqrt ((x - 1)^2)) = A^2"
    by (smt (verit) mult_cancel_left2 one_power2 power2_diff)
  then have "2 * (x + (sqrt ((x - 1)^2))) = A^2"
    by simp
  then have "2 * (x + abs (x - 1)) = A^2" using sqrt_abs
    by auto
  then show ?thesis by auto
qed


subsection "part a"


lemma IMO1959_p2_a:
  fixes x::real
  assumes "2 * x - 1 \<ge> 0"
  assumes "x - sqrt (2 * x - 1) \<ge> 0"
  assumes "A = sqrt 2"
  shows "\<forall>x::real. (x < ((1/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> A)"
      "\<forall>x::real. (x > (1::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> A)"
      "\<forall>x::real. ((x \<ge> ((1/2)::real)) \<and> (x \<le> (1::real))) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = A)"
  using assms
proof - 
  show a1:"\<forall>x::real. (x < ((1/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> A)"
    by blast
  show a2: "\<forall>x::real. (x > (1::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> A)"
    by blast
  show a3: "\<forall>x::real. ((x \<ge> ((1/2)::real)) \<and> (x \<le> (1::real))) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = A)"
    using numeral_le_one_iff semiring_norm(69) by blast
qed

subsection "part b"
lemma IMO1959_p2_b:
  fixes x::real
  assumes "2 * x - 1 \<ge> 0"
  assumes "x - sqrt (2 * x - 1) \<ge> 0"
  assumes "A = sqrt 2"
  shows "\<forall>x::real. (x < ((1/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> A)"
      "\<forall>x::real. (x > (1::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> A)"
      "\<forall>x::real. ((x \<ge> ((1/2)::real)) \<and> (x \<le> (1::real))) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = A)"
  sorry

subsection "part c"


end