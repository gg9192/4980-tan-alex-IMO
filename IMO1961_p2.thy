theory IMO1961_p2
  imports "HOL-Analysis.Simplex_Content"
begin         
section "proof"

lemma diff_of_squares:
  fixes a b::real
  shows "(a-b)*(a+b) = a^2 - b^2 "
  by (simp add: power2_eq_square square_diff_square_factored)

lemma neq_squares:
  fixes a b:: real
  assumes "a > 0" "b > 0" "a \<noteq> b"
  shows "a^2 \<noteq> b^2"
  using assms(1) assms(2) assms(3) by auto

lemma IMO1961p2:
  fixes A B C :: "real ^ 2"
  assumes "A \<noteq> B"
  assumes "C \<noteq> B"
  assumes "A \<noteq> C"
  assumes "a = dist B C"
  assumes "b = dist A C" 
  assumes "c = dist A B"
  assumes "S = content (convex hull {A, B, C})"
  assumes "s = (a + b + c) / 2"
  shows "(a^2) + (b^2) + (c^2) \<ge> 4 * S * (sqrt 3)"
  using assms
proof -
  have heron:"S = sqrt (((a + b + c)/2)*((-a + b + c)/2)*((a - b + c)/2)*((a + b - c)/2))"
  proof - 
    have heron1: "S = sqrt (s * (s - a) * (s - b) * (s - c))" 
      using heron assms by blast
    show ?thesis using assms(5)
    proof -
      have f1: "s - c \<le> (a + b - c) / 2"
        by (simp add: assms(8))
      have f2: "(a + b - c) / 2 \<le> s - c"
        by (simp add: assms(8))
      then have f3: "(a + b - c) / 2 = s - c"
        using f1 by simp
      have f4: "(a - b + c) / 2 = s - b"
        using f2 f1 by simp
      have "(- a + b + c) / 2 = s - a"
        using f2 f1 by simp
      then show ?thesis
        using f4 f3 assms(8) heron1 by presburger
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
    have a4: "sqrt ((?A + ?B + ?C)^2) \<ge> sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
      using a3
      using real_sqrt_le_iff by presburger
    have a5: "?A + ?B + ?C \<ge> sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
      using a4
      by auto
    have a6:"sqrt (3 * ((4 * (b ^ 2) * (c ^ 2)) - (b\<^sup>2 + c\<^sup>2 - a\<^sup>2)\<^sup>2)) = sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
    proof - 
      have replace:  "sqrt (3 * ((4 * (b ^ 2) * (c ^ 2)) - (b\<^sup>2 + c\<^sup>2 - a\<^sup>2)\<^sup>2)) = sqrt (3 * ((4 * ?B * ?C) - (?B + ?C - ?A)\<^sup>2))"
        by auto
      have a1:"(?B + ?C - ?A)\<^sup>2 = (?B^2) + 2 * ?B * ?C - 2 * ?A * ?B - 2 * ?A * ?C + (?A^2) + (?C^2)"
        by algebra
      have a2: " sqrt (3 * ((4 * ?B * ?C) - (?B + ?C - ?A)\<^sup>2)) =  sqrt (3 * ((4 * ?B * ?C) - ((?B^2) + 2 * ?B * ?C - 2 * ?A * ?B - 2 * ?A * ?C + (?A^2) + (?C^2))))"
        using a1
        by presburger 
      have a3: " sqrt (3 * ((4 * ?B * ?C) - ((?B^2) + 2 * ?B * ?C - 2 * ?A * ?B - 2 * ?A * ?C + (?A^2) + (?C^2)))) =  sqrt (3 * ((4 * ?B * ?C) - (?B^2 + 2 * ?B * ?C - 2 * ?A * ?B - 2 * ?A *?C + ?A^2 + ?C^2)))"
        by blast
        show ?thesis using replace a1 a2 a3
          by argo
    qed
    have a7: "sqrt (3 * (4 * b\<^sup>2 * c\<^sup>2 - (b\<^sup>2 + c\<^sup>2 - a\<^sup>2)\<^sup>2)) \<le> a\<^sup>2 + b\<^sup>2 + c\<^sup>2" using a5 a6
      by linarith
    show ?thesis using a7 rhs
      by presburger
  qed
qed

section "equality"  

lemma IMO1961p2_eq:
  fixes A B C :: "real ^ 2"
  assumes "A \<noteq> B"
  assumes "C \<noteq> B"
  assumes "A \<noteq> C"
  assumes "a = dist B C"
  assumes "b = dist A C" 
  assumes "c = dist A B"
  assumes "S = content (convex hull {A, B, C})"
  assumes "s = (a + b + c) / 2"
  shows "(a^2) + (b^2) + (c^2) = 4 * S * (sqrt 3) \<longleftrightarrow> (a = b \<and> b = c)"
  using assms
proof -  
  { assume a1: "a = b \<and> b = c"
    have ?thesis using a1 sorry}
  moreover {assume a2: "a \<noteq> b \<or> b \<noteq> c \<or> a \<noteq> c"
    have heron:"S = sqrt (((a + b + c)/2)*((-a + b + c)/2)*((a - b + c)/2)*((a + b - c)/2))"
      proof - 
        have heron1: "S = sqrt (s * (s - a) * (s - b) * (s - c))" 
          using heron assms(4-8) by blast
        show ?thesis using assms(5)
        proof -
          have f1: "s - c \<le> (a + b - c) / 2"
            by (simp add: assms(8))
          have f2: "(a + b - c) / 2 \<le> s - c"
            by (simp add: assms(8))
          then have f3: "(a + b - c) / 2 = s - c"
            using f1 by simp
          have f4: "(a - b + c) / 2 = s - b"
            using f2 f1 by simp
          have "(- a + b + c) / 2 = s - a"
            using f2 f1 by simp
          then show ?thesis
            using f4 f3 assms(8) heron1 by presburger
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
      let ?A = "a^2"
      let ?B = "b^2"
      let ?C = "c^2"
      have rhs_simp: "4 * S * sqrt 3 = sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
      proof -
        have a1: "4 * S * sqrt 3 = 4 * ((1/4)::real) * sqrt ((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - b ^ 2 - c ^ 2 + a ^ 2)) * sqrt (3)"
          using dist
          by fastforce
        have id: "4 * ((1/4)::real) = 1"
          by auto
        have a2: "4 * S * sqrt 3 =  sqrt ((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - b ^ 2 - c ^ 2 + a ^ 2)) * sqrt (3)"
          using a1 id
          by simp
        have a3: "sqrt ((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - b ^ 2 - c ^ 2 + a ^ 2)) * sqrt (3) =  sqrt ((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - (b ^ 2 + c ^ 2 - a ^ 2))) * sqrt (3)"
          by simp
        have dos: "(2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - (b ^ 2 + c ^ 2 - a ^ 2)) = 4*b^2*c^2 - (b^2 + c ^ 2 - a ^ 2)^2" 
          using diff_of_squares[of "2 * b * c" "b\<^sup>2 + c\<^sup>2 - a\<^sup>2"]
          by (smt (verit, best) add.commute add.left_commute four_x_squared minus_diff_eq mult.commute power_mult_distrib uminus_add_conv_diff) 
        have a4: "sqrt ((2 * b * c + b ^ 2 + c ^ 2 - a ^ 2) * (2 * b * c - (b ^ 2 + c ^ 2 - a ^ 2))) * sqrt (3) = sqrt (4*b^2*c^2 - (b^2 + c ^ 2 - a ^ 2)^2) * sqrt (3)"
          using dos a3
          by presburger
        have a5: "sqrt (4*b^2*c^2 - (b^2 + c ^ 2 - a ^ 2)^2) * sqrt (3) = sqrt (3*(4*b^2*c^2 - (b^2 + c ^ 2 - a ^ 2)^2))"
          by (metis (no_types, opaque_lifting) mult.commute real_sqrt_mult) 
        have distb: "3*(4*b^2*c^2 - (b^2 + c ^ 2 - a ^ 2)^2) = (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
          by algebra
        have a6: "sqrt (3*(4*b^2*c^2 - (b^2 + c ^ 2 - a ^ 2)^2)) = sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
          using distb
          by presburger
        show ?thesis using a1 a2 a3 a4 a5 a6
          by presburger
      qed
      have gt: "?A + ?B + ?C > sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 *?C * ?A - 3 * ?A^2 - 3 * ?B ^ 2 - 3 * ?C ^ 2)"
      proof - 
        have all_gt_0: "a > 0 \<and> b > 0 \<and> c > 0" using assms
         by simp
        have a1: "?A^2 + ?B^2 + ?C ^2 > ?A * ?B + ?B * ?C + ?C * ?A"
        proof - 
          have aa: "((?A^2 + ?B^2)/2) + ((?B^2 + ?C^2)/2) + ((?C^2 + ?A^2)/2) > ?A * ?B + ?B * ?C + ?C * ?A"
          proof -
            {assume asm1: "a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
              have "(?A - ?B)^2 > 0" using asm1
                by (simp add: all_gt_0 neq_squares)
              then have "?A^2 - ?A * ?B * 2 + ?B^2 > 0"
                by (simp add: power2_diff)
              then have "?A^2 + ?B^2 >  ?A * ?B * 2"  
                by argo
              then have f1: "((?A^2 + ?B^2)/2) > ?A * ?B" using asm1
                by simp
              have ?thesis using f1
                by (meson add_mono_thms_linordered_field(3) arith_geo_mean power_mult_distrib zero_le_power2)}
            moreover {assume asm2: "a = b \<and> b \<noteq> c \<and> a \<noteq> c"
              have f1: "((?A^2 + ?B^2)/2) = ?A * ?B" using asm2
                by simp
              have f2: "((?B^2 + ?C^2)/2) > ?B * ?C"
              proof - 
                have "(?B - ?C)^2 > 0" using asm2
                  by (simp add: all_gt_0 neq_squares)
                then have "?B^2 - 2*?B*?C + ?C^2 > 0"
                  by (simp add: power2_diff)
                then show ?thesis
                  by fastforce  
              qed
              have ?thesis using f1 f2
                by (smt (verit, del_insts) asm2 mult.commute)}
            moreover {assume asm3: "a \<noteq> b \<and> b = c \<and> a \<noteq> c"
              have eq: "(?B^2 + ?C^2)/2 = ?B * ?C" using asm3
                by simp 
              have "(?A - ?B)^2 > 0" using asm3
                by (simp add: all_gt_0 neq_squares)
              then have "?A^2 - ?A * ?B * 2 + ?B^2 > 0"
                by (simp add: power2_diff)
              then have "?A^2 + ?B^2 >  ?A * ?B * 2"  
                by argo
              then have f1: "((?A^2 + ?B^2)/2) > ?A * ?B" using asm3
                by simp
               have ?thesis using eq f1
                 by (smt (verit, del_insts) asm3 mult.commute)}
             moreover {assume asm4: "a \<noteq> b \<and> b \<noteq> c \<and> a = c"
               have eq: "(?C^2 + ?A^2)/2 = ?C * ?A" using asm4
                 by simp
               have "(?A - ?B)^2 > 0" using asm4
                by (simp add: all_gt_0 neq_squares)
              then have "?A^2 - ?A * ?B * 2 + ?B^2 > 0"
                by (simp add: power2_diff)
              then have "?A^2 + ?B^2 >  ?A * ?B * 2"  
                by argo
              then have f1: "((?A^2 + ?B^2)/2) > ?A * ?B" using asm4
                by simp
               have ?thesis using eq f1
                 by (smt (verit, del_insts) asm4 mult.commute)}
             moreover {assume asm5:"a = b \<and> b = c \<and> a \<noteq> c"
               have eq: "(?A^2 + ?B^2)/2 = ?A * ?B" using asm5
                 by simp
               have gt: "((?C^2 + ?A^2)/2) > ?C * ?A" using asm5
                 by force
               have ?thesis using eq gt
                 using asm5 by force}
             moreover {assume asm6:"a = b \<and> b \<noteq> c \<and> a = c"
               have eq: "(?A^2 + ?B^2)/2 = ?A * ?B" using asm6
                 by simp
               have gt: "((?B^2 + ?C^2)/2) > ?B * ?C"
                 using asm6 by blast
               have ?thesis using eq gt
                 using asm6 by blast}
             {assume asm7:"a \<noteq> b \<and> b = c \<and> a = c"
               have gt: "(?A^2 + ?B^2)/2 > ?A * ?B" using asm7
                 by auto
              have ?thesis using gt
                using asm7 by force}
              ultimately show ?thesis
                using a2 by blast
          qed
          have ab: "((?A^2 + ?B^2)/2) + ((?B^2 + ?C^2)/2) + ((?C^2 + ?A^2)/2) = ?A^2 + ?B^2 + ?C^2"
            by argo
        show ?thesis using aa ab
          by force
        qed
        have a2: "4 * ?A^2 + 4 * ?B^2 + 4 * ?C ^2 > 4 * ?A * ?B + 4 * ?B * ?C + 4 * ?C * ?A" using a1
          by linarith
        have a3: "?A^2 + ?B^2 + ?C ^2 > 4 * ?A * ?B + 4 * ?B * ?C + 4 * ?C * ?A - 3 * ?A^2 - 3 * ?B^2 - 3 * ?C^ 2" 
          using a2
          by argo
        have a4: "?A^2 + ?B^2 + ?C^2 + 2 * ?A * ?B + 2 * ?B * ?C + 2 * ?C * ?A > 6 * ?A * ?B + 6 * ?B * ?C + 6 * ?C * ?A - 3 * ?A^2 - 3 * ?B^2 - 3 * ?C^ 2"
          using a3
          by argo
        have lhs: "?A^2 + ?B^2 + ?C^2 + 2 * ?A * ?B + 2 * ?B * ?C + 2 * ?C * ?A = (?A + ?B + ?C) ^ 2"
          by algebra
        have rewrite: "(?A + ?B + ?C) ^ 2 > 6 * ?A * ?B + 6 * ?B * ?C + 6 * ?C * ?A - 3 * ?A^2 - 3 * ?B^2 - 3 * ?C^ 2"
          using lhs a4 
          by presburger
        have last: "?A + ?B + ?C > sqrt (6 * ?A * ?B + 6 * ?B * ?C + 6 * ?C * ?A - 3 * ?A^2 - 3 * ?B^2 - 3 * ?C^ 2)" 
          using rewrite
          by (meson add_nonneg_nonneg real_less_lsqrt zero_le_power2) 
        show ?thesis using last
          try0
          by blast
      qed
      have ?thesis using rhs_simp gt
        using assms(7) 
        using calculation by argo  
  }
  ultimately show ?thesis 
    by fastforce  
qed



end