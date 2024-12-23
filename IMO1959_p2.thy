theory IMO1959_p2
  imports "HOL-Computational_Algebra.Euclidean_Algorithm" "HOL.Real"  "HOL.NthRoot"
begin         

section "helper lemmas"

lemma sqrt_abs:
  fixes x::real
  shows "sqrt (x^2) = abs x"
  using real_sqrt_abs by blast

lemma eq_simp:
  (* this lemma handles all the messy algebra that all three parts rely on. *)
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
  (* this is part a of the problem. We use implication to show that as long as x in in a certain range
  then the equation =/!= some value *)
  fixes x::real
  assumes "2 * x - 1 \<ge> 0"
  assumes "x - sqrt (2 * x - 1) \<ge> 0"
  shows " (x < ((1/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> (sqrt 2))"
      "(x > (1::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> (sqrt 2))"
      "((x \<ge> ((1/2)::real)) \<and> (x \<le> (1::real))) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = (sqrt 2))"
  using assms
proof - 
  show " (x < ((1/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> (sqrt 2))"
    using assms(1) by linarith
  show "(x > (1::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> (sqrt 2))"
    using assms(2) eq_simp by fastforce
  show "((x \<ge> ((1/2)::real)) \<and> (x \<le> (1::real))) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = (sqrt 2))"
    by (smt (verit, ccfv_SIG) assms(1) assms(2) eq_simp pos2 power2_eq_imp_eq real_root_le_iff real_root_pow_pos2 real_sqrt_zero sqrt_def)
qed

subsection "part b"

lemma IMO1959_p2_b:
  (* this is part b of the problem. We use implication to show that as long as x in in a certain range
  then the equation =/!= some value *)
  fixes x::real
  assumes "2 * x - 1 \<ge> 0"
  assumes "x - sqrt (2 * x - 1) \<ge> 0"
  shows "(sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> 1)"
  using assms
proof -
  {assume "x < ((1/2)::real)"
    then have ?thesis using assms
      by simp}
  moreover {assume "x \<ge> ((1/2)::real) \<and> x \<le> 1"
    then have ?thesis using IMO1959_p2_a assms(2) 
      by auto}
  moreover {assume "x > 1"
    then have ?thesis
      by (smt (verit) assms(2) real_sqrt_ge_0_iff real_sqrt_ge_1_iff sqrt_ge_absD sqrt_le_D)}
  ultimately show ?thesis
    by linarith
qed
subsection "part c"

lemma IMO1959_p2_c:
  (* this is part c of the problem. We use implication to show that as long as x in in a certain range
  then the equation =/!= some value *)
  fixes x::real
  assumes "2 * x - 1 \<ge> 0"
  assumes "x - sqrt (2 * x - 1) \<ge> 0"
  shows " (x < ((3/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> 2)"
      "(x > ((3/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> 2)"
      "(x = ((3/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = 2)"
  using assms
proof -
  show "(x < ((3/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> 2)"
    by (smt (z3) assms(1) assms(2) eq_simp field_sum_of_halves four_x_squared one_le_power)
  show "(x > ((3/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) \<noteq> 2)"
    using assms(2) eq_simp by fastforce
  have "(x = ((3/2)::real)) \<Longrightarrow> ( 2 * (x + abs(x - 1)) = 2^2)"
    by force
  then show "(x = ((3/2)::real)) \<Longrightarrow> (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = 2)"
     using eq_simp
     by (smt (verit) assms(2) field_sum_of_halves real_sqrt_ge_0_iff real_sqrt_unique) 
qed

end