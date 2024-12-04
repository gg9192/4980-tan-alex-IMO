theory IMO2011_p5

imports Main

begin

(* Define arbitrary function f *)
consts f:: "int \<Rightarrow> int"

(* Stating assumptions. Using modular instead of straight dvd helps easing the proving process.*)
locale f_assms = 
  assumes f_pos: "\<forall>m::int. f(m) > 0"
  assumes f_div: "\<forall>m n::int. (f(m) - f(n)) mod f(m - n) = 0"


(* Fact 1: f(m) dvd f(0) *)
lemma (in f_assms) fact_1: 
  shows "f(m) dvd f(0)"
proof -
  have h1: "f(m) dvd (f(m) - f(0))" 
    using f_div f_pos
    by (metis diff_0_right mod_eq_0_iff_dvd)
  have h2: "\<exists>k::int. f(m) - f(0) =  k*f(m)"
    using h1 
    by auto  
  then obtain k::"int" where o1: "f(m) - f(0) = k*f(m)"
    by auto
  then have h6: "f(m) = f(0) + k*f(m)"
  proof -
    have h61: "f(m) - f(0) + f(0) = k*f(m) + f(0)"
      using o1
      by simp
    then have h62: "f(m) - f(0) + f(0) = f(m) + f(0) - f(0)"
      by simp
    have h63: "f(0) - f(0) = 0"
      by simp
    then have h64: "f(m) + f(0) - f(0) = f(m)"
      by simp
    then have h65: "f(m) - f(0) + f(0) = f(m)"
      using h62
      by simp  
    then show ?thesis
      using h61
      by simp   
  qed
  then have h7: "f(m) - k*f(m) = f(0)"
    by auto
  then have h3: "f(0) = f(m) - k*f(m)"
    by simp 
  then have h4: "f(0) = f(m)*(1-k)"
    by (simp add: mult.commute right_diff_distrib')  
  then have h5: "f(m) dvd f(0)"
    by simp
  then show "f(m) dvd f(0)"
    by simp
qed

(* Fact 2: f(m) = f(-m) *)
lemma (in f_assms) fact_2: 
  shows "f(m) = f(-m)"
proof -
  have h1: "f(m) dvd (f(0) - f(-m))"
    by (metis add.inverse_inverse f_div mod_eq_0_iff_dvd verit_minus_simplify(3))
  then have h2: "f(m) dvd f(-m)"
    using f_pos fact_1
    by (metis dvd_imp_mod_0 mod_0_imp_dvd mod_eq_dvd_iff)
  then have h3: "f(-m) dvd f(m)"
    using f_pos fact_1
    by (metis diff_0 diff_0_right dvd_imp_mod_0 dvd_minus_iff dvd_minus_mod f_div mod_diff_left_eq)
  show ?thesis
    using h2 h3 dvd_antisym
    by (meson f_pos nless_le zdvd_antisym_nonneg)
qed

(* Fact 3: f(m) dvd f(k*m) *)
lemma (in f_assms) fact_3_helper: 
  fixes k:: int
  assumes "k > 0"
  shows "\<forall>m::int. f(m) dvd f(k * m)"
  using assms
proof (induct k)
  case base
  then show ?case
    by auto
next
  case (step i)
  then show ?case 
  proof (clarify)
    fix m
    have h1: "f(m) dvd (f((i + 1) * m) - f(i * m))" 
      using f_div
      by (smt (verit) dvd_eq_mod_eq_0 mult.commute mult_cancel_left1 right_diff_distrib')
    then show "f(m) dvd f((i + 1) * m)" 
      using step zdvd_zdiffD
      by blast
  qed
qed

lemma (in f_assms) fact_3:
  fixes k:: int
  shows "\<forall>m::int. f(m) dvd f(k * m)"
proof (clarsimp)
  fix m
  have a1: "\<forall>k::int. f(k * m) = f(-k * m)"
    using fact_2 
    by force
  {assume a1: "k = 0" 
    have a11: "f(m) dvd f(k * m)" 
      using fact_1 a1
      by force  
  }
  show "f(m) dvd f(k * m)"
    using a1 fact_1 fact_3_helper
    by (metis linorder_neqE_linordered_idom mult_eq_0_iff neg_less_0_iff_less)
qed
                                                          

(* Fact 4: If f(a) dvd f(ax+b) then f(a) dvd f(b)*)
lemma (in f_assms) fact_4: 
  assumes "f(a) dvd f(a * x + b)"
  shows "f(a) dvd f(b)"
  using assms
proof -
  have h1: "f(a * x) dvd (f(a * x + b) - f(b))"
    using f_div fact_1
    by (metis diff_add_cancel group_cancel.sub1 mod_eq_0_iff_dvd)
  then have h2: "f(a) dvd (f(a * x + b) - f(b))"
    using fact_3
    by (metis dvd_trans mult.commute)
  have h3: "f(a) dvd f(b)"
    using h1 h2 fact_3
    by (metis assms mod_eq_0_iff_dvd mod_eq_dvd_iff)
  show ?thesis
    using h3
    by blast
qed

(* Lemma 1: Suppose m \<noteq> n and f(m) \<le> f(n), if |n - m| dvd n, then f(m) dvd f(n) *)
lemma (in f_assms) lemma_1: 
  assumes "m \<noteq> n"
  assumes "f(m) \<le> f(n)"
  shows "abs (n - m) dvd n \<Longrightarrow> f(m) dvd f(n)"
  using assms
proof -
  let ?d = "abs (n - m)"
  assume "?d dvd n"
  have h1: "f(n) dvd (f(?d) - f(m))"
    using fact_2
    by (smt (verit) diff_right_commute f_div mod_eq_0_iff_dvd)
  have h2: "f(?d) dvd f(n)"
    using f_div fact_1 fact_3
    by (metis \<open>\<bar>n - m\<bar> dvd n\<close> dvd_def mult.commute)
  then have h3: "f(?d) \<le> f(n)"
    using f_div dvd_imp_le f_assms_axioms f_assms_def zdvd_imp_le 
    by blast 
  have h4: "f(m) = f(?d)"
    using f_pos h1 h3 assms(2)
    by (smt (verit, del_insts) dvd_imp_le_int)
  show "f(m) dvd f(n)"
    using h2 h4
    by presburger
qed

(* Main problem *)
theorem (in f_assms) 
  assumes "f(m) \<le> f(n)"
  assumes "m > 0" and "n > 0" (*WLOG*)
  shows "f(m) dvd f(n)"
  using assms
proof -
  let ?g = "gcd n m"
  have h1: "\<exists>x y::int. m*x = n*y + ?g"
    by (metis bezout_int minus_add_cancel mult.commute mult_minus_right)
  then obtain x y::"int" where " m*x = n*y + ?g"
    by auto  
  have h2: "?g = m*x - n*y"
    by (simp add: \<open>m * x = n * y + gcd n m\<close>)
  have h3: "?g dvd m*x"
    by simp
  have h4: "?g dvd n*y"
    by simp
  {assume a1: "f(m*x) \<le> f(n*y)"
    then have h51: "f(m*x) dvd f(n*y)"
      using lemma_1
      using \<open>m * x = n * y + gcd n m\<close> assms(3) 
      by auto
    then have h52: "f(m) dvd f(m*x - ?g)"
      using h2 fact_3
      by (metis add_diff_cancel_left' diff_diff_eq2 dvd_trans mult.commute)
    then have h53: "f(m) dvd f(?g)"
    proof -
      have h531: "f(m) dvd f(m*0 - ?g)"
        using fact_4 h52 by auto
      then have h534: "f(m) dvd f(0 - ?g)"
        by simp 
      then have h532: "f(m) dvd f(-?g)"
        by simp
      then have h533: "f(-?g) = f(?g)"
        using fact_2
        by simp
      then show ?thesis
        using h532 by presburger   
    qed
    then have h54: "f(m) dvd f(n)"
      using fact_3
      by (metis dvdE dvd_trans gcd.commute gcd_dvd2 mult.commute) 
    then have ?thesis
      by simp  
  } moreover {assume a2: "f(m*x) > f(n*y)"
    then have h61: "f(n*y) dvd f(m*x)"
      using h2 h3 lemma_1
      by (metis abs_gcd_int order_less_imp_le order_less_irrefl)
    then have h62: "f(n) dvd f(?g)"      
      by (smt (verit, ccfv_threshold) Groups.mult_ac(2) dvd_trans f_assms.fact_3 f_assms.fact_4 f_assms_axioms h2 mult_eq_0_iff nonzero_mult_div_cancel_left)
    have h63: "f(?g) dvd f(n)"
      using fact_3
      by (metis dvdE gcd.commute gcd_dvd2 mult.commute)
    have h64: "f(?g) dvd f(m)"
      using fact_3
      by (metis dvdE gcd_dvd2 mult.commute)
    then have h65: "f(?g) = f(m)"
      using f_pos h62 h63 assms(1)
      by (metis verit_la_disequality zdvd_imp_le)
    have h66: "f(m) dvd f(n)"
      using h63 h65 
      by auto
    then have ?thesis
      by simp 
  }
  ultimately show ?thesis
    by linarith
qed

end