theory IMO1961_p2
  imports "HOL-Analysis.Simplex_Content"
begin         
section "proof"

lemma IMO1961p2:
  fixes A B C :: "real ^ 2"
  assumes "a = dist B C"
  assumes "b = dist A C" 
  assumes "c = dist A B"
  assumes "S = content (convex hull {A, B, C})"
  assumes "s = (a + b + c) / 2"
  shows "(a^2) + (b^2) + (c^2) \<ge> 4 * s * (sqrt 3)"
  using assms
proof -
  have heron:"S = sqrt (((a + b + c)/2)*((-a + b + c)/2)*((a - b + c)/2)*((a + b - c)/2))"
  proof - 
    have heron1: "S = sqrt (s * (s - a) * (s - b) * (s - c))" 
      using heron assms(1-5) by blast
    show ?thesis using assms(5)
    proof -
      have f1: "s - c \<le> (a + b - c) / 2"
        by (simp add: assms(5))
      have f2: "(a + b - c) / 2 \<le> s - c"
        by (simp add: assms(5))
      then have f3: "(a + b - c) / 2 = s - c"
        using f1 by simp
      have f4: "(a - b + c) / 2 = s - b"
        using f2 f1 by simp
      have "(- a + b + c) / 2 = s - a"
        using f2 f1 by simp
      then show ?thesis
        using f4 f3 assms(5) heron1 by presburger
    qed
  qed 
  have factor: "S = (1/4) * sqrt ((a + b + c)*(-a + b + c)*(a - b + c)*(a + b - c))" 
  proof -
    have fac1: "S = sqrt ((1/16)*((a + b + c)*(-a + b + c)*(a - b + c)*(a + b - c)))"
      using local.heron by auto 
    then have mult: "sqrt ((1/16)*((a + b + c)*(-a + b + c)*(a - b + c)*(a + b - c))) = sqrt (1/16) * sqrt ((a + b + c)*(-a + b + c)*(a - b + c)*(a + b - c)) "
      using real_sqrt_mult by blast
    have simp: "sqrt ((1/16)::real) = ((1/4)::real)"
      using real_sqrt_divide by fastforce
    show ?thesis using fac1 mult simp
      by presburger 
  qed
  have dist: "S = (1/4) * sqrt ((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - b ^ 2 - c ^ 2 + a ^ 2))"
  proof -
    have alg1: "(a + b + c)*(-a + b + c) = (2 * b * c + b ^ 2 + c ^ 2 - a ^ 2)"
    proof - 
      have a1: "(a + b + c)*(-a + b + c) = - (a ^ 2) + a * b + a * c - b * a  + b ^ 2 + b * c -a * c + c * b + c^ 2"
        by (smt (verit, del_insts) combine_common_factor distrib_left mult.commute power2_eq_square)
      show ?thesis using a1
        by simp
    qed
    have alg2:  "(a - b + c)*(a + b - c) = (2 * b * c - b ^ 2 - c ^ 2 + a ^ 2)"
    proof -
      have a1: "(a - b + c)*(a + b - c) = a ^ 2 + a * b - a * c - b * a - b ^ 2 + b * c + c * a + c * b - c ^ 2"
        by (smt (verit) diff_add_eq diff_diff_eq2 left_diff_distrib power2_eq_square right_diff_distrib)
      show ?thesis using a1
        by force
    qed
    show ?thesis using alg1 alg2
      by (simp add: factor)  
  qed
  show ?thesis sorry
qed
value "1/(4::nat)"

section "equality"

end