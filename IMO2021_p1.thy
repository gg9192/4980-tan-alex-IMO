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



lemma diff_at_least_one_exist_int:
  fixes a b::real
  assumes "a > b"
  shows "a - b \<ge> 1 \<Longrightarrow> (\<exists>e::int. e \<ge> b \<and> e \<le> a)"
proof -
  assume "a - b \<ge> 1"
  then have "a \<ge> b + 1" 
    by simp
  then have "a \<ge> b + 1" 
    by simp
  then have blt: "b \<le> floor a"
    using assms
    by linarith
  then have flalte: "floor a \<le> a" 
    by (simp add: floor_less_iff)
  then show  "(\<exists>e::int. b \<le> e \<and> e \<le> a)" using blt flalte
    by blast 
qed

lemma simplify:
  fixes n:: int
  assumes "n \<ge> 107"
  shows "sqrt (1 + n) - sqrt (1 + (n/2)::real ) -2 \<ge> 1"
proof - 
  have simplify: "sqrt (1 + n) - sqrt (1 + (n/2)::real ) -2 \<ge> 1"
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
  then show ?thesis by auto
qed

lemma equation_simp:
  fixes n:: int
  assumes "n \<ge> 107"
  shows "\<exists> e::int. (2 * e * (e - 2) \<ge> n \<and> 2 * e * (e + 2) \<le> 2 * n) \<and> (2 * e^2 + 1 < 2 * n \<and> 2 * e^2 + 1 > n) \<and> e > 1"
  using assms
proof -

  have "sqrt (1 + n) - 1 - (sqrt (1 + (n/2) + 1)) \<ge> 1" using simplify
    by (smt (verit) assms field_sum_of_halves of_int_1 of_int_power_le_of_int_cancel_iff one_power2 real_sqrt_one sqrt_add_le_add_sqrt)
  let ?upper_bound = "sqrt (1 + n) - 1"
  let ?lower_bound = "sqrt (1 + (n / 2)) + 1"
  have "\<exists>e::int. e \<ge> ?lower_bound \<and> e \<le> ?upper_bound"
  proof - 
    have p1: "?lower_bound < ?upper_bound" using assms
      using simplify[of "n"] by argo     
    show ?thesis using diff_at_least_one_exist_int p1 simplify[of "n"] assms
      by auto
  qed
  then obtain e::int where e_fact: "e \<ge> ?lower_bound \<and> e \<le> ?upper_bound"
    by blast
  have a1: "n \<le> 2 * e * (e - 2)"
  proof -
    have "sqrt (1 +  (n / 2)) + 1 \<le> e" using e_fact
      by auto
    then have c1: "sqrt (1 +  (n / 2)) \<le> e - 1"
      by force
    then have "1 +  (n / 2) \<le> e^2 - 2 * e + 1"
    proof -
      have d1: "(e - 1) ^ 2 =  e^2 - 2 * e + 1"
        by algebra
      have d2: "(sqrt (1 + real_of_int n / 2))^2 = (1 + real_of_int n / 2)"
        using assms by auto
      then show ?thesis using c1 d1 d2
        by (metis of_int_power_eq_of_int_cancel_iff sqrt_le_D)
    qed
    then have "(n / 2) \<le> e^2 - 2 * e"
      by simp
    then have "n \<le> 2 * e^2 - 4 * e"
      by linarith
    then have "n <= 2 * (e^2 - 2 * e)"
      by presburger
    then show ?thesis
      by (metis left_diff_distrib mult.commute mult.left_commute power2_eq_square) 
  qed
  have a2: " e * (e + 2) \<le>  n"
  proof - 
    have "e \<le> sqrt (1 + n) - 1" using e_fact
      by auto
    then have c1: "e + 1 \<le> sqrt (1 + n)"
      by simp
    then have "e^2 + 2 * e + 1 \<le> 1 + n"
    proof - 
      have a1: "(e + 1)^2 = e^2 + 2 * e + 1"
        by (simp add: comm_semiring_class.distrib power2_eq_square ring_class.ring_distribs(1))
      have a2: "1 + n = (sqrt (1 + n))^2"
        using assms by auto
      have a3: "(1 + e)^2 \<le> (sqrt (1 + n))^2" using c1 assms
        by (smt (verit, best) a2 e_fact field_sum_of_halves of_int_0_le_iff of_int_eq_of_int_power_cancel_iff real_less_lsqrt real_sqrt_ge_zero)
        
      show ?thesis using a1 a2 a3
        by (metis add.commute of_int_le_iff)
    qed
    then show ?thesis
      by (simp add: distrib_left power2_eq_square)
  qed
  have egt1: "e > 1"
    using assms e_fact
    by (smt (verit, ccfv_SIG)  field_sum_of_halves of_int_1_less_iff real_sqrt_le_iff real_sqrt_one)
  then have "2 * e * (e - 2) <  2 * e\<^sup>2 + 1 \<and> 2 * e\<^sup>2 + 1 < 2 * e * (e + 2)"
  proof - 
    have a1: "2 * e * (e - 2) <  2 * e\<^sup>2 + 1"
    proof -
      have "-4 * e < 1"
        using egt1 by linarith
      then have "2 * e ^2 - 4 * e < 2 * e^2 + 1"
        by simp
      then show ?thesis
        by (smt (z3) int_distrib(3) mult_less_cancel_left power2_diff)
    qed
    have a2: " 2 * e\<^sup>2 + 1 < 2 * e * (e + 2)"
      by (smt (z3) egt1 mult_less_cancel_left one_power2 power2_diff right_diff_distrib)
    show ?thesis using a1 a2
      by meson
  qed
  then show ?thesis using a1 a2 egt1
    by force
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
    {assume asm: "n \<ge>100 \<and> n < 107"
      let ?a = "126::int"
      let ?b = "163::int"
      let ?c = "198::int"
      have aneq: "?a \<noteq> ?b \<and> ?a \<noteq> ?c \<and> ?b \<noteq> ?c"
        by presburger
      have amemb: "?a \<in> cards \<and> ?b \<in> cards \<and> ?c \<in> cards" using asm
      proof - 
        have a: "?a \<in> cards" using asm assms(3)
        proof -
            {assume "n=100"
              have "126 \<in> {(100::int)..200}"
                by simp
              then have ?thesis using asm
                using assms(3) by auto  }
            moreover  {assume a:  "n=101"
              have "126 \<in> {(101::int)..202}"
                by simp
              then have ?thesis
                using assms(3) a
                by force }
             moreover  {assume a: "n=102"
              have "126 \<in> {(102::int)..204}"
                by simp
              then have ?thesis using assms(3) a
                by simp }
             moreover  {assume a: "n=103"
              have "126 \<in> {(103::int)..206}"
                by simp
              then have ?thesis using asm 
              by (simp add: assms(3))}
             moreover  {assume a: "n=104"
              have "126 \<in> {(104::int)..208}"
                by simp
              then have ?thesis using assms(3) a by force}
             moreover  {assume a: "n=105"
              have "126 \<in> {(105::int)..210}"
                by simp
              then have ?thesis using assms(3) a by force}
             moreover  {assume a: "n=106"
              have "126 \<in> {(106::int)..212}"
                by simp
              then have ?thesis using assms(3) a by force}
            ultimately show ?thesis using asm
              by fastforce
          qed
          have b: "?b \<in> cards"
          proof - 
            {assume a: "n = 100"
              then have "?b \<in> {(100::int)..200}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover { assume a: "n = 101"
              then have "?b \<in> {(101::int)..202}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover { assume a: "n = 102"
              then have "?b \<in> {(102::int)..202}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover { assume a: "n = 103"
              then have "?b \<in> {(103::int)..206}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover { assume a: "n = 104"
              then have "?b \<in> {(104::int)..208}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover { assume a : "n = 105"
              then have "?b \<in> {(105::int)..210}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a: "n = 106"
              then have "?b \<in> {(106::int)..212}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            ultimately show ?thesis using asm
              by fastforce
          qed
          have c: "?c \<in> cards"
          proof - 
            {assume a: "n = 100"
              then have "?c \<in> {(100::int)..200}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a: "n = 101"
              then have "?c \<in> {(101::int)..202}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a: "n = 102"
              then have "?c \<in> {(102::int)..204}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a: "n = 103"
              then have "?c \<in> {(103::int)..206}"
                by simp 
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a: "n = 104"
              then have "?c \<in> {(104::int)..208}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a: "n = 105"
              then have "?c \<in> {(105::int)..210}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            moreover {assume a : "n = 106"
              then have "?c \<in> {(106::int)..212}"
                by simp
              then have ?thesis using a assms(3) 
                by auto}
            ultimately show ?thesis using asm by force
          qed
          show ?thesis using a b c
            by blast
        qed
      have aps: "((perfect_square (?a + ?b)) \<and> (perfect_square (?a + ?c)) \<and> (perfect_square (?c + ?b)))"
      proof - 
        have a1: "perfect_square (?a + ?b)"
        proof - 
          have a1: "?a + ?b = 17^2"
            by auto
          then  show ?thesis
            by (metis perfect_square_def power2_eq_square)
        qed
        have a2: "(perfect_square (?a + ?c))"
        proof - 
          have "?a + ?c = 18^2"
            by simp
          then show ?thesis unfolding perfect_square_def
            by (metis power2_eq_square) 
        qed
        have a3: "(perfect_square (?c + ?b))"
        proof - 
          have "?c + ?b = 19^2"
            by simp
          then show ?thesis unfolding perfect_square_def 
            by (metis power2_eq_square)
        qed
        show ?thesis using a1 a2 a3 by presburger
      qed
      then have ?thesis using aneq aps amemb 
        by blast}
    moreover {assume gt: "n \<ge> 107"
      have "\<exists> e::int. (2 * e * (e - 2) \<ge> n \<and> 2 * e * (e + 2) \<le> 2 * n) \<and> (2 * e^2 + 1 < 2 * n \<and> 2 * e^2 + 1 > n) \<and> e > 1"
        using equation_simp
        using gt by blast 
      then obtain e where e_literal: "(2 * e * (e - 2) \<ge> n \<and> 2 * e * (e + 2) \<le> 2 * n) \<and> (2 * e^2 + 1 < 2 * n \<and> 2 * e^2 + 1 > n) \<and> e > 1"
        by blast
      let ?a = "(2 * e * (e - 2))"
      let ?b = "2 * e^2 + 1"
      let ?c = "(2 * e * (e + 2))"
      have egt1: "e > 1" using e_literal
        by blast
      have member: "?a \<in> cards \<and> ?b \<in> cards \<and> ?c \<in> cards" using e_literal
      proof -
        let ?upper_bound = "sqrt (1 + n) - 1"
        let ?lower_bound = "sqrt (1 + (n / 2)) + 1"
        have amemb:"?a \<in> {n..2*n}" using e_literal
        proof -
          have lower: "?a \<ge> n"
            using e_literal by blast
          have upper: "?a \<le> 2*n"
          proof -
            have a1: "?b > ?a" using egt1
              by (simp add: power2_eq_square)
            have "?c > ?b"
              by (smt (verit, best) egt1 less_1_mult power2_diff right_diff_distrib)
            then show ?thesis using a1
              using e_literal by linarith 
          qed
          show ?thesis using lower upper
            using atLeastAtMost_iff by blast 
        qed
        have bmemb: "?b \<in> {n..2*n}"
          using e_literal
          by (meson atLeastAtMost_iff order_less_le) 
        have cmemb: "?c \<in> {n..2*n}"
        proof -
          have a1: "?b > ?a" using egt1
              by (simp add: power2_eq_square)
          have "?c > ?b"
            by (smt (verit, best) egt1 less_1_mult power2_diff right_diff_distrib)
          then show ?thesis using a1
            using atLeastAtMost_iff e_literal less_le_not_le order_trans by auto
          qed
          then show ?thesis using amemb bmemb cmemb assms(3)
          by meson
      qed
      have aps: "perfect_square (?a + ?b) \<and> perfect_square (?a + ?c) \<and> perfect_square (?c + ?b)"
      proof - 
        have ps1: "perfect_square (?a + ?b)"
        proof - 
          have "?a + ?b = (2*e - 1)^2"
          proof -
            have "(2*e - 1)^2 = 2 * e * 2 * e - 2 * e - 2 * e + 1"
              by algebra
            then have "(2*e - 1)^2 = 4 * e^2 - 4 * e + 1"
              by (simp add: power2_diff)
            then have "(2*e - 1)^2 = 2 * e^2  + 2 * e^2 - 4 * e + 1"
              by simp
            then have d1: "(2*e - 1)^2 = 2 * e^2 - 4 * e + 2 * e^2+ 1"
              by presburger
            have "2 * e^2 - 4 * e = 2 * e * ( e - 2)"
            proof - 
              have a1: "2 * e^2 - 4 * e = e * (2 * e - 4)"
                by algebra
              then have "e * (2 * e - 4) = 2 * e * (e - 2)"
                by auto
              then show ?thesis using a1 
                by auto
            qed
            then show ?thesis using d1
              by presburger
          qed
          then show ?thesis unfolding perfect_square_def
            using power2_eq_square by auto 
          qed
        have ps2: "perfect_square (?a + ?c)"
        proof -
          have "?a + ?c = 4 * e ^2"
          proof -
            have a1: "2 * e * (e - 2) + 2 * e * (e + 2) = 2 * e ^ 2 + 2 * e + 2 * e ^ 2 - 2 * e" 
              by algebra
            have a2: " 2 * e ^ 2 + 2 * e + 2 * e ^ 2 - 2 * e = 2 * e^2 + 2 * e^2"
              by presburger
            show ?thesis using a1 a2 try0
              by fastforce
          qed
          then show ?thesis unfolding perfect_square_def
            by (smt (z3) distrib_left)
        qed
        have ps3: "perfect_square (?c + ?b)"
        proof -
          have "?c + ?b = (2 * e + 1)^2"
          proof -
            have a1: " 2 * e * (e + 2) + (2 * e\<^sup>2 + 1) = 2 * e^2 + 4 * e + 2 * e^2 + 1"
              by algebra
            have a2: "2 * e^2 + 4 * e + 2 * e^2 + 1 = 4 * e^2 + 4 * e + 1"
              by auto
            then show ?thesis using a1 a2
              by (simp add: distrib_left mult.commute power2_eq_square)
          qed
          then show ?thesis unfolding perfect_square_def
            power2_eq_square by auto
        qed
        show ?thesis using ps1 ps2 ps3
          by blast
      qed
      have aneq: "?a \<noteq> ?b \<and> ?a \<noteq> ?c \<and> ?b \<noteq> ?c \<and> ?a \<noteq> ?c"
      proof - 
        have a1: "?a \<noteq> ?b"
        proof - 
          have a1: "?b > ?a" using egt1
            by (simp add: power2_eq_square)
          then show ?thesis
            by force
        qed
        have a2: "?a \<noteq> ?c"
          using e_literal by auto
        have a3: "?b \<noteq> ?c"
          by (smt (z3) e_literal less_1_mult power2_diff right_diff_distrib)
        show ?thesis using a1 a2 a3
          by blast 
      qed
      then have ?thesis using member aps aneq
        by blast}
    ultimately show ?thesis
    using assms(1)
    by fastforce
  qed
  then show ?thesis
    by (metis Un_iff assms(4))
qed

end