theory IMO1961_p2
  imports "HOL-Analysis.Simplex_Content"
begin         
section "proof"

lemma diff_of_squares:
  fixes a b::real
  shows "(a-b)*(a+b) = a^2 - b^2 "
  by (simp add: power2_eq_square square_diff_square_factored)
    

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
  have diff_of_squares: "S = (1/4) * sqrt ((4*b^2*c^2)- ((b^2 + c^2-a^2)^2))" 
  proof - 
    have s1: "((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - b ^ 2 - c ^ 2 + a ^ 2)) = (2 * b * c)\<^sup>2 - (b\<^sup>2 + c\<^sup>2 - a\<^sup>2)\<^sup>2"
      using diff_of_squares[of "2 * b * c" "b^2 + c^2-a^2"] dist
      by (smt (verit, del_insts) mult.commute)
    have s2: "(2 * b * c)\<^sup>2 = 4*b^2*c^2"
      by algebra
    show ?thesis using s1 s2
      using dist by presburger
  qed
  have rhs: "4*S*(sqrt 3) = sqrt (3 * ((4 * (b ^ 2) * (c ^ 2)) - (b\<^sup>2 + c\<^sup>2 - a\<^sup>2)\<^sup>2))"
  proof - 
    have d1: "4 * S * (sqrt 3) = 4 * ((1/4)::real) * sqrt ((4*b^2*c^2)- ((b^2 + c^2-a^2)^2)) * sqrt 3" using dist
      by (simp add: local.diff_of_squares)    
    have numbers: " 4 * ((1/4)::real) = 1"
      by simp
    show ?thesis using d1 numbers
      by (metis (no_types, opaque_lifting) mult.commute mult_1 real_sqrt_mult)
  qed
  let ?A = "a^2"
  let ?B = "b^2"
  let ?C = "c^2"
  have amgm1: "(?A^2 + ?B^2) / 2 \<ge> ?A * ?B"
    using arith_geo_mean power_mult_distrib zero_le_power2 by blast
  have amgm2: "(?B^2 + ?C^2) / 2 \<ge> ?B * ?C"
    by (meson arith_geo_mean power_mult_distrib zero_le_power2)
  have amgm3: "(?C^2 + ?A^2) / 2 \<ge> ?C * ?A "
    using arith_geo_mean power_mult_distrib zero_le_power2 by blast
  have laststep: "((?A^2 + ?B^2) / 2) + ((?B^2 + ?C^2) / 2) + ((?C^2 + ?A^2) / 2)\<ge> ?A * ?B + ?B * ?C + ?C * ?A" using amgm1 amgm2 amgm3
    by argo
  have last_simp: "?A^2 + ?B^2 + ?C^2\<ge> ?A * ?B + ?B * ?C + ?C * ?A" using laststep
    by argo
    
  show ?thesis
  proof - 
    have a1: "4 * ?A^2 + 4 * ?B^2 + 4 * ?C^2\<ge> 4 * ?A * ?B + 4 * ?B * ?C + 4 * ?C * ?A" using last_simp  
      by linarith
    have a2: "?A^2 + ?B^2 + ?C^2 + 2 * ?A * ?B + 2 * ?B * ?C + 2 * ?C * ?A \<ge> 6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2"
      using a1
      by argo
    have simp_lhs: "(?A + ?B + ?C)^2 = ?A^2 + ?B^2 + ?C^2 + 2 * ?A * ?B + 2 * ?B * ?C + 2 * ?C * ?A"
      by algebra
    have a3: "(?A + ?B + ?C)^2 \<ge>6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2"
      using a2 simp_lhs
      by presburger
    show ?thesis sorry
  qed
qed

section "equality"

end