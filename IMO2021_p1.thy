theory IMO2021_p1
  imports Complex_Main


begin

definition perfect_square :: "int \<Rightarrow> bool" where
  "perfect_square n \<longleftrightarrow> (\<exists>k. n = k * k)"

lemma sqrt_sqr:
  fixes x::real
  assumes "x \<ge> 0"
  shows "sqrt (x^2) = x"
  by (simp add: assms)


lemma equation_simp:
  fixes n:: int
  assumes "n \<ge> 107"
  shows "\<exists> e::int. (2 * e * (e - 2) \<ge> n \<and> 2 * e * (e + 2) \<le> 2 * n)"
  using assms
proof -
  fix e::int
  have "sqrt (1 + n) - sqrt (1 + (n/2)::real ) -2 \<ge> 1"
  proof -
    have "n \<ge> 107 \<Longrightarrow> n^2 - 108 * n + 180 \<ge> 0"
    proof - 
      assume a1:  "n \<ge> 107"
      have c1: "(n-54)^2 \<ge> 2736" using a1
      proof - 
        {assume a1: "n = 107"
          have "(n-54)^2 = 2809" using a1
            by simp
          then have ?thesis using a1
            by auto}
        moreover {assume a2: "n > 107"
          then have a3: "n - 54 > (53::int)"
            by auto
          have "(53::int) ^ 2 = 2809"
            by auto
          then have "(n - 54)^2 > 2809" using a3
            by (smt (verit, ccfv_SIG) pos2 power_mono_iff)
          then have ?thesis
            by linarith}
        ultimately show ?thesis using a1
          by fastforce
      qed
      then have "n^2 - 108*n + 2916 \<ge> 2736"
      proof -
        have a1: "(n - 54)^2 = (n - 54) * (n - 54)"
          using power2_eq_square by blast
        have a2: "(n - 54) * (n - 54) = n^2 - 54 * n -54 * n + 2916"
          by algebra
        have "2736 \<le> n^2 - 54 * n -54 * n + 2916 " using c1 a1 a2
          by argo 
        then show ?thesis using c1 by presburger
      qed
      then show ?thesis
        by force
    qed
    then have "n^2 - 108 * n + 180 \<ge> 0" using assms
      by blast
    then have "(1/4) * n^2 - 27 * n + 45 \<ge> 0"
      by linarith
    then have "(1/4) * n^2 \<ge>  27 * n - 45"
      by linarith
    then have "(1/4) * n^2 \<ge> (9 * n + 18 * n) + (36 - 81)"
      by simp
    then have "(1/4) * n^2 - 9 * n + 81 \<ge> 18 * n + 36"
      by linarith
    then have "(1/4) * n^2 - 9 * n + 81 \<ge> 36* (1/2 * n + 1)"
      by auto
    then have d1:  "(1/4) * n^2 - 18 * 1/2 * n + 81 \<ge> 36* (1/2 * n + 1)"
      by auto
    then have c3: "(1/2 * n - 9)^2 >= 36* (1/2 * n + 1)"
    proof - 
      have a1: "(1/2 * n - 9)^2 = (1/2 * n - 9) * (1/2 * n - 9)"
        by algebra
      have a2: "(1/2 * n - 9) * (1/2 * n - 9) = (1/2) * (1/2) * n^2 - 9 * 1/2 * n - 9 * 1/2 * n + (-9) * (-9)"
      proof -
        have "- (real 9 * 1 / real 2 * real_of_int n) + (- (real 9 * 1 / real 2 * real_of_int n) + 1 / real 2 * (1 / real 2) * real_of_int (n\<^sup>2)) + - (real 9 * - real 9) = - real 9 * (- real 9 + real_of_int n * (1 / real 2)) + (real_of_int n * - (real 9 * (1 / real 2)) + real_of_int n * (real_of_int n * (1 / real 2 * (1 / real 2))))"
          by (simp add: power2_eq_square)
        then have "- (real 9 * 1 / real 2 * real_of_int n) + (- (real 9 * 1 / real 2 * real_of_int n) + 1 / real 2 * (1 / real 2) * real_of_int (n\<^sup>2)) + - (real 9 * - real 9) = (- real 9 + 1 / real 2 * real_of_int n) * (- real 9 + 1 / real 2 * real_of_int n)"
          by argo
        then show ?thesis
          by simp
      qed
    then show ?thesis using a1 a2
      using d1 by auto 
  qed
  then have "6 * sqrt (1 / 2 * real_of_int n + 1) \<le> 1 / 2 * real_of_int n - 9" 
  proof - 
    have a1:"sqrt (36* (1/2 * n + 1)) = sqrt 36 * sqrt (1/2 * n + 1)"
      using real_sqrt_mult by blast 
    have a2: "sqrt 36 * sqrt (1/2 * n + 1) = 6 * sqrt (1/2 * n + 1)"
    proof - 
      have a3: "sqrt 36 = 6"
        by auto
      have a4: "sqrt 36 * sqrt (((1/2)::real) * n + 1) = 6 * sqrt (1/2 * n + 1)"
        using a3 by presburger
      then show ?thesis using a3 a4
        by presburger
    qed
    have "1 / 2 * real_of_int n - 9 \<ge> 0"
      using assms
      by simp   
    then have c4:  "sqrt (((((1 / 2)::real) * real_of_int n - 9)\<^sup>2)::real) = ((1/2)::real)* real_of_int n - 9"
      using sqrt_sqr[of "1 / 2 * real_of_int n - 9"]
      by blast
    then show ?thesis using c3 c4
      by (metis a1 a2 real_sqrt_le_iff)
  qed
  then have "1 + (1/2) * n \<ge> 10 + 6 * sqrt (1 + (n/2))"
    by argo
  then have "1 + n \<ge> 10 + 6 * sqrt (1 + (n/2)) + (n/2)"
    by auto
  then have b1:  "1 + n \<ge> 9 + 6 * sqrt (1 + (n/2)) + 1 + (n/2)"
    by auto
  then have "1 + n \<ge> (3 + sqrt (1 + (n/2))) * (3 + sqrt (1 + (n/2)))"
  proof - 
    have "9 + 6 * sqrt (1 + (n/2)) + 1 + (n/2) = (3 + sqrt (1 + (n/2))) * (3 + sqrt (1 + (n/2)))"
    proof - 
      have a1: "(3 + sqrt (1 + (n/2))) * (3 + sqrt (1 + (n/2))) = 3 * 3 + 3 * sqrt (1 + (n/2)) + 3 * sqrt (1 + (n/2)) + sqrt (1 + (n/2)) * sqrt (1 + (n/2))"
        by algebra
      have a2: "3 * 3 + 3 * sqrt (1 + (n/2)) + 3 * sqrt (1 + (n/2)) + sqrt (1 + (n/2)) * sqrt (1 + (n/2)) = 9 + 6 * sqrt (1 + (n/2)) + 1 + (n/2)"
        using assms by auto
      show ?thesis using a1 a2
        by presburger
    qed
    then show ?thesis using b1
      by presburger
  qed
  then have "(3 + sqrt (1 + real_of_int n / 2))^2 \<le> real_of_int (1 + n)"
    by (simp add: power2_eq_square)
  then have "(3 + sqrt (1 + real_of_int n / 2)) \<le> sqrt (real_of_int (1 + n))"
    by (simp add: real_le_rsqrt)
  then have "sqrt (1 + real_of_int n / 2) \<le> sqrt (real_of_int (1 + n)) - 3"
    by simp
  then show ?thesis
    by argo      
qed



lemma IMO2021_p1:
  fixes n::int
  fixes p1 p2::"int set"
  fixes cards::"int set"
  assumes "n \<ge> 100"
  assumes "p1 \<inter> p2 = {}"
  assumes "cards = {n..2*n}"
  assumes "p1 \<union> p2 = cards"
  shows "(\<exists>a b::int. (a \<in> p1 \<and> b \<in> p1) \<and> (a \<noteq> b) \<and> (perfect_square (a + b))) \<or> (\<exists>a b::int. (a \<in> p2 \<and> b \<in> p2) \<and> (a \<noteq> b) \<and> (perfect_square (a + b))) "
proof - 
  have ex_3: "\<exists> a b c::int. (a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> a \<noteq> c) \<and> (a \<in> cards \<and> b \<in> cards \<and> c \<in> cards) \<and> ((perfect_square (a + b)) \<and> (perfect_square (a + c)) \<and> (perfect_square (c + b)) \<and> (perfect_square (a + c)) ) "
  proof - 
    {assume "n = 100"
      then have ?thesis sorry }
    moreover {assume "n = 101" 
      then have ?thesis sorry}
    moreover {assume "n = 102" 
      then have ?thesis sorry}
    moreover {assume "n = 103" 
      then have ?thesis sorry}
    moreover {assume "n = 104" 
      then have ?thesis sorry}
    moreover {assume "n = 105" 
      then have ?thesis sorry}
    moreover {assume "n = 106" 
      then have ?thesis sorry}
    moreover {assume "n \<ge> 107"
      have "\<exists> e::int. (2 * e * (e - 2) \<ge> n \<and> 2 * e * (e + 2) \<le> 2 * n) "
        sorry
      then have ?thesis sorry}
    ultimately show ?thesis
    using assms(1) by fastforce 
  qed
  then show ?thesis
    by (metis Un_iff assms(4))
qed

end