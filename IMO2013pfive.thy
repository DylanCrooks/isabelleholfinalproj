theory IMO2013pfive
  imports Complex_Main HOL.Limits
begin


section "HelperLemmas"
(*this is used *)
lemma positive_rational_signs:
  fixes x :: rat
  assumes "x = Fract p q"
  shows "x > 0 \<longleftrightarrow> (p > 0 \<and> q > 0) \<or> (p < 0 \<and> q < 0)"
proof -
  have "x > 0 \<longleftrightarrow> (Fract p q > 0)" using assms by simp
  also have "\<dots> \<longleftrightarrow> (p * q > 0)"
    using less_rat_def positive_rat by auto 
  also have "\<dots> \<longleftrightarrow> (p > 0 \<and> q > 0) \<or> (p < 0 \<and> q < 0)"
    by (simp add: zero_less_mult_iff)
  finally show ?thesis .
qed

(*used in krat2_global *)
lemma ftest:
  fixes f:: "rat \<Rightarrow>real"
  fixes x y a :: "rat"
  fixes m n:: "int"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
   "\<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)"  (*claim1 *)
shows "(x = Fract m n) \<and> (m > 0) \<and> (n>0) \<Longrightarrow> f (x) > 0 "
proof -
(*actually non-trivial
Prove by assuming antecedent.
Then we show that if (f x) \<le> 0, it leads to a contradiction. *)
  assume passm: "(x = Fract m n) \<and> (m > 0) \<and> (n>0)"
  then have mn_gt_0: "(m > 0) \<and> (n>0)" by auto
  have xmn: "x = (Fract m n)" using passm by auto
    have m_gt_0: "m>0" using mn_gt_0 by auto
    have n_gt_0: "n>0" using mn_gt_0 by auto
    have x_gt_0: "x > 0" using passm by (simp add: zero_less_Fract_iff) 
    have "(f x) > 0" proof -
      have "(\<not>(f x) > 0) \<Longrightarrow> False" proof -
        assume "\<not>( (f x) > 0)"
        then have assms_fk_lte_0: "(f x) \<le> 0" by auto 
        
        define ma na::rat where ma_def: "ma = (rat_of_int m)" and na_def: "na = (rat_of_int n)"         
       then have c123: "(ma > na) \<or> (ma < na) \<or> (ma = na)"
         by linarith
        (*for contradiction proof, we split into three cases.
either m = n, m > n, or m < n. *)

        have c1: "(ma > na) \<Longrightarrow> (\<not>(f x) > 0 \<Longrightarrow> False)"
        proof - 
          have x_eq_mn: "x = ma/na" using ma_def na_def Fract_of_int_quotient
            by (simp add: \<open>x = Fract m n \<and> 0 < m \<and> 0 < n\<close>) 
          have na_gt_0: "na > 0" using n_gt_0 na_def by simp
          have ma_gt_0: "ma > 0" using m_gt_0 ma_def by simp 
          have fma_gt_0: "(f ma) > 0" using m_gt_0 assms(4)[of m]
            by (simp add: ma_def)
          have fna_gt_0: "(f na) > 0" using n_gt_0 assms(4)[of n]
            by (simp add: na_def)
(*For m>n case, we prove that (f m) and (f n) are greater than zero, using claim1.
Because we've proved claim1 in f_is_identity, we add it as an assumption in this helperlemma *)
          have "( (f na)* (f x) \<ge> (f ma))" 
             using assms(1)[of ma na] mn_gt_0 na_gt_0 ma_gt_0 x_eq_mn
             by (metis assms(1) x_gt_0 less_imp_neq mult.commute nonzero_eq_divide_eq)
(*Using the multiplication assumption and x = ma/na,  we say that f(na) * (f x) \<ge> (f ma)
Then, by contra hyps, we have (f (na) * (f x) \<le> 0, because (f x) \<le>0
then, (f ma \<le>0, but also (f ma) \<ge> 0, so we have a contradiction. *)
          then have "(f (na)) * (f (x)) \<le> 0" using assms_fk_lte_0 fma_gt_0 fna_gt_0
            by (simp add: mult_le_0_iff)
          then have "(f(ma)) \<le> 0"
            using assms(1)[of na x] x_eq_mn xmn na_def ma_def  \<open>f ma \<le> f na * f x\<close> by linarith
          then have "False"
            using fma_gt_0 by auto
          then show ?thesis by simp qed
        (*The m<n case proceeds as the m>n case. We prove that (f m) > 0, and (f m) \<le> (f x) * (f n),
and (f n) * (f x) \<le> 0, so 0 \<ge> (f m), wihch is a contradiction. *)
        have c2:"(ma < na) \<Longrightarrow> (\<not>(f x) > 0 \<Longrightarrow> False)" proof - 
          have x_eq_mn: "x = ma/na"
            by (simp add: Fract_of_int_quotient xmn ma_def na_def) 
          have na_gt_0: "na > 0" using n_gt_0 na_def by simp
          have ma_gt_0: "ma > 0" using m_gt_0 ma_def by simp 
          have fma_gt_0: "(f ma) > 0" using m_gt_0 assms(4)[of m]
            by (simp add: ma_def)
          have fna_gt_0: "(f na) > 0" using n_gt_0 assms(4)[of n]
            by (simp add: na_def)
          have "( (f na)* (f x) \<ge> (f ma))" 
             using assms(1)[of ma na] mn_gt_0 na_gt_0 ma_gt_0 x_eq_mn
             by (metis assms(1) x_gt_0 less_imp_neq mult.commute nonzero_eq_divide_eq)
          then have "(f (na)) * (f (x)) \<le> 0" using assms_fk_lte_0 fma_gt_0 fna_gt_0
            by (simp add: mult_le_0_iff)
          then have "(f(ma)) \<le> 0"
            using assms(1)[of na x] x_eq_mn xmn na_def ma_def  \<open>f ma \<le> f na * f x\<close> by linarith
          then have "False"
            using fma_gt_0 by auto
          then show ?thesis by simp qed
        have c3: "(ma = na) \<Longrightarrow> (\<not>(f x) > 0 \<Longrightarrow> False)"
        proof - 
(*for the m=n case, we prove that x=1, so (f x) = (f 1), and using claim1, (f 1) \<ge> 1, which contradicts
(f x) < 0. *)
          assume "ma = na"
          then have "x=1"
            using Fract_of_int_quotient xmn ma_def mn_gt_0 na_def by auto
          then  show ?thesis using assms(4)
            by (smt (verit) \<open>\<not> 0 < f x\<close> of_int_1) qed 
        then have "False" using c1 c2 c3 c123 using assms_fk_lte_0 by auto
        then show ?thesis  by auto qed
      then show ?thesis by auto qed
    then show ?thesis by auto qed 


(*here, we assume krat2_global (proved later) and claim1, and the f_is_identity assumptions, and we prove 
(f (x^n)) \<le> (f x)^n. mgg is used in various other helper lemmas.   *)
lemma mgg:
  fixes f:: "rat \<Rightarrow>real"
  fixes x y a :: "rat"
  fixes m n:: "int"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
   "\<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)"  (*claim1 *)
 " \<And>k. 0 < k \<Longrightarrow> 0 < f k" (* krat2_global *)
 shows  "\<And>x n. 0 < x \<Longrightarrow> 0 < n \<Longrightarrow> f (x ^ n) \<le> f x ^ n"
proof -
  obtain a::"rat" where a_prop: "a > 1 \<and> f a = (real_of_rat) a" using assms(3) by auto
  have claim1:  " \<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)" using assms(4) by simp
  have krat2a:  " \<And>k. 0 < k \<Longrightarrow> 0 < f k" using assms(5) by simp
          fix x::"rat"
          fix n::"nat"
          assume x_gt_0: "x>0"
          assume n_gt_0: "n>0" 
          have f1_gt_1:  "f 1 \<ge> 1" using a_prop  by (metis assms(1) comm_monoid_mult_class.mult_1 dual_order.strict_trans less_numeral_extra(1) mult_le_cancel_right1 zero_less_of_rat_iff)

(*to prove, we fix x and n to satisfy the assumptions. 
then we case split on n=1 and n>1. n=1 case is proved trivially. *)

          show " f (x ^ n) \<le> f x ^ n" using n_gt_0
          proof -
            have n_gte_1:"n>1 \<or> n=1" using n_gt_0 by fastforce 
            have n_eq_1_case:"n=1 \<Longrightarrow>  f (x ^ n) \<le> f x ^ n"
            proof -
              assume n_eq_1: "n=1"
              have  fx1:"(f (x ^ n)) = (f x)" using n_eq_1 by auto
              then have fx2: "((f x) ^ n) = (f x)" using n_eq_1 by auto
              then show ?thesis using fx1 fx2 by simp qed
            have n_gt_1_case: "n>1 \<Longrightarrow>  f (x ^ n) \<le> f x ^ n" 

          proof (induct n)
            case 0
            then show ?case  by simp 
          next
            case (Suc n)
            have "(x ^ (Suc n)) = x * (x ^ n)" by simp
            then have h2: "f (x ^ (Suc n)) \<le> (f x) * (f (x ^ n))" using assms(1) by (simp add: x_gt_0)
            have h1:  "(f x)^ (Suc n) = (f x) * ((f x)^n)" by simp
            have c10: "n > 0 \<or> n = 0" using n_gt_0 by auto
            
            then show ?case proof -

              have case1: "n > 0 \<Longrightarrow> f (x ^ Suc n) \<le> f x ^ Suc n"
              proof -
                assume n_gt_0: "n > 0"
                have fx_gt_0: "f x > 0"  using krat2a[of x] assms(1) assms(2) assms(3) claim1 x_gt_0 by blast 
                have "(f x) * (f (x ^ n)) \<le> (f x) * ((f x)^n)" using Suc.hyps n_gt_0 x_gt_0 fx_gt_0
                  using Suc.prems less_Suc_eq_le by force 
           (*for the n>1 case, we induct on n. 
f ^ (suc n) = (f ^ n) * f. Then we split by cases, and prove that if n>0, then f(x^suc n) \<le> (f x)^(suc n).
We use assms(1) to say that (f (x^suc n)) \<ge> (f n) * (f (x^n)), so we replace the LHS with a potentially smaller and more restricted value, and
prove it for that case using the induction hypothesis. This completes the lemma.  *)

                then show ?thesis
                  using h2 by auto  qed
              then show ?thesis using case1  c10 by auto  qed qed
          then show ?thesis using n_eq_1_case n_gt_1_case n_gte_1 by auto qed qed

lemma krat2_global:
  fixes f:: "rat \<Rightarrow>real"
  fixes x y a :: "rat"
  fixes m n:: "int"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
   "\<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)"  (*claim1 *)
 shows  " \<And>k. 0 < k \<Longrightarrow> 0 < f k"
proof -
  have claim1:  "\<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)" using assms(4) by simp
  fix k::"rat"
  assume k_gt_0: "k>0"
(*for proving krat2, we assume claim1, and then split our k into two integers. We then case split, using positive_rational_signs, to prove
the lemma when p2/q2 are both positive, and when they are both negative.  *)
  obtain p2 q2::int where kp2q2: "k = Fract p2 q2"
        proof -
          assume a1: "\<And>p2 q2. k = Fract p2 q2 \<Longrightarrow> thesis"
          obtain ii :: "(rat \<Rightarrow> bool) \<Rightarrow> int" and iia :: "(rat \<Rightarrow> bool) \<Rightarrow> int" and iib :: "(rat \<Rightarrow> bool) \<Rightarrow> int" and iic :: "(rat \<Rightarrow> bool) \<Rightarrow> int" where
            "\<forall>p r. p r \<or> \<not> p (Fract (ii p) (iia p)) \<and> 0 < iia p"
            by (metis Rat_induct_pos)
          then show ?thesis
            using a1 by auto
        qed 

   have gtlt0:  "(p2 > 0 \<and> q2 > 0) \<or> ( p2 < 0 \<and> q2 < 0)" using kp2q2 k_gt_0
     by (simp add: positive_rational_signs)
(*positive case is split off into a helper lemma, ftest. *)
      have fkp2q2: "(p2>0 \<and> q2>0) \<Longrightarrow> ( (f k) > 0)"
      proof -
        assume p2q2_gt_0: "(p2>0 \<and> q2>0)"
        show ?thesis using ftest[of f k p2 q2]
          by (simp add: assms(1) assms(2) assms(3) claim1 kp2q2 p2q2_gt_0) qed

      have fkp3q3: "(p2<0 \<and> q2<0) \<Longrightarrow> ( (f k) > 0)"proof - 
        assume p2q2_lt_0: "(p2<0 \<and> q2<0)"
        then have "(-p2)>0 \<and> (-q2)>0" by simp 
        define p2i q2i::int where "p2i = (-p2)" and "q2i = (-q2)"
        have "Fract p2i q2i = Fract p2 q2" by (simp add: p2i_def q2i_def) 
        then have "k = (Fract p2i q2i)" by (simp add: kp2q2) 
        then have "p2i > 0 \<and> q2i > 0"  using \<open>0 < - p2 \<and> 0 < - q2\<close> p2i_def q2i_def by auto 
        then have "(f k) > 0" using ftest[of f k p2i q2i] assms(1) assms(2)
            assms(3) claim1 kp2q2 p2q2_lt_0 \<open>k = Fract p2i q2i\<close> by blast
        then show ?thesis by auto qed 
   
(*For the negative case, we show that reversing the sign  of both numerator and denominator doesn't change the fraction
then we prove (f k) > 0 by using ftest on the now positive numerator and denominator  *)   
       show "0 < (f k)" using fkp3q3 fkp2q2
         using gtlt0 by blast 
     qed




(*the following helper lemma is useful for the proving f_is_identity's case for x=1.  *)
  lemma sublinear:
    fixes f:: "rat \<Rightarrow> real"
    fixes x y a :: "rat"
    assumes 
    "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
    "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
    "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
   
  shows "\<And>x n. 0 < x \<Longrightarrow> 0 < n \<Longrightarrow> real_of_int n * f x \<le> f (rat_of_int n * x)"
proof -
  fix x::"rat"
  assume x_gt_0: "x>0"
      fix n::"int"
      assume n_gt_0: "0 < n"
      show "real_of_int n * f x \<le> f (rat_of_int n * x)" proof - 
            (*to prove this, we fix n, but we prove the case where n is fixed, to avoid errors 
with quantification and goal refinement. We prove this by induction, using step i.
Importantly, we induct on the fixed n in this case. Figuring out how to induct on two variables
was difficult, and dealing with two variables in general was the most difficult part of 
formalizing this problem.
Additionally, in proving this helper lemma, we don't assume claim1, as this lemma is used in the proof of claim1
 *)

        have subthing: "\<And>x::rat. x > 0 \<Longrightarrow> f((rat_of_int n) * x) \<ge> (real_of_int n)  * (f(x))"
        proof -
          fix x::"rat"
          assume x_gt_0: "x>0"
          show  "f((rat_of_int n) * x) \<ge> (real_of_int n)  * (f(x))"  using n_gt_0 x_gt_0
          proof (induct n arbitrary:x)
            case base
            then show ?case by auto
          next
            case (step i)
            have h0: "f (rat_of_int (i + 1) * x) = f (((rat_of_int i)*x) + x)"
              by (simp add: ring_class.ring_distribs(2))
              
            have h1: "(rat_of_int i) * x > 0" using step.hyps step.prems by auto
            then have h2: "(f ( (rat_of_int i) * x)) + (f x)  \<le> f (((rat_of_int i) * x) + x)"
            using assms(2)[of "(rat_of_int i) * x" x] step by auto 
            then have h3: " real_of_int (i + 1) * f x  = ((real_of_int i) * (f x)) +  f x"
            by (simp add: distrib_left mult.commute) 
          then have  "(real_of_int i) * (f x) \<le> f((rat_of_int i)*x) " using step.hyps(2)[of x] step.prems(1) h1 h2 h3
            by simp
          then have h5: "((real_of_int i) * (f x)) + (f x) \<le>  f((rat_of_int i)*x) + (f x)" by auto
            then show ?case unfolding h3 h0  using h1 h2 h3 h5 by auto
          qed
        qed
        show ?thesis
          by (simp add: subthing x_gt_0)  qed qed

lemma claim1_global:
  fixes f:: "rat \<Rightarrow> real"
  fixes x y a :: "rat"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
shows " \<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)"
proof -
  obtain a::rat where a_prop: "a > 1 \<and> f a = (real_of_rat) a " using assms(3) by auto
      fix n::"int"
      assume n_gt_0: "0 < n"
      show " f (rat_of_int n) \<ge> real_of_int n" proof - 
            
        have subthing: "\<And>x::rat. x > 0 \<Longrightarrow> f((rat_of_int n) * x) \<ge> (real_of_int n)  * (f(x))"
        proof -
          fix x::"rat"
          assume x_gt_0: "x>0"
          show  "f((rat_of_int n) * x) \<ge> (real_of_int n)  * (f(x))"  using n_gt_0 x_gt_0
          proof (induct n arbitrary:x)
            case base
            then show ?case by auto
          next
            case (step i)
            have h0: "f (rat_of_int (i + 1) * x) = f (((rat_of_int i)*x) + x)"
              by (simp add: ring_class.ring_distribs(2))
              
            have h1: "(rat_of_int i) * x > 0" using step.hyps step.prems by auto
            then have h2: "(f ( (rat_of_int i) * x)) + (f x)  \<le> f (((rat_of_int i) * x) + x)"
            using assms(2)[of "(rat_of_int i) * x" x] step by auto 
            then have h3: " real_of_int (i + 1) * f x  = ((real_of_int i) * (f x)) +  f x"
            by (simp add: distrib_left mult.commute) 
          then have  "(real_of_int i) * (f x) \<le> f((rat_of_int i)*x) " using step.hyps(2)[of x] step.prems(1) h1 h2 h3
            by simp
          then have h5: "((real_of_int i) * (f x)) + (f x) \<le>  f((rat_of_int i)*x) + (f x)" by auto
            then show ?case unfolding h3 h0  using h1 h2 h3 h5 by auto
          qed
        qed
          
(*to prove claim1, we copy the proof of "subthing" from the helper lemma "sublinear"
then we use assms(1) and the property of fixed point a to get (f 1) \<ge> 1.
Combining this and subthing, we get (f n) \<ge>   n(f 1)  \<ge> n * 1, for all n>0.
f does not accept 0 or any negatives as part of its domain.
 *)


   
      then have " f (a * 1) = real_of_rat a" using a_prop  assms(1)[of a 1] using subthing by auto
      then have "real_of_rat a * (f 1) \<ge> real_of_rat a" using a_prop assms(1)[of a 1] by simp
      then have f1_case:  "f 1 \<ge> 1" using a_prop mult_cancel_left1 by auto 
      then show ?thesis  using subthing[of 1]
      by (smt (verit) less_numeral_extra(1) mult_cancel_left1 mult_le_cancel_left1 n_gt_0 of_int_nonneg)
      qed
      qed

(*then, we prove f is strictly increasing.
Here, dealing with quantifiers and multiply variables was difficult. In proving this, I proved
various helper lemmas, namely krat2. *)
lemma f_strict1_global: 
  fixes f:: "rat \<Rightarrow> real"
  fixes x y a :: "rat"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
 

shows " \<And>i j. 0 < i \<Longrightarrow> 0 < j \<Longrightarrow> j < i \<Longrightarrow> f j < f i"
 proof -
   fix i j::"rat"
   assume i_gt_0: "i>0"
   assume i_gt_j: "i>j"
   assume j_gt_0: "j>0"
(*to prove this, we let r = i-j. i>j by assms, so r>0.
we have (f i) and f(r) >0 by krat2. 
we have (f (j+r) as a substitue for (f i), and we use assms(2) to say it's greater than or equal to (f j) + (f r)
Then, because both (f j) and (f r) are nonzero, (f i) will be greater than (f i)  subtracting either. *)
   have krat2: " \<And>k. 0 < k \<Longrightarrow> 0 < f k" using krat2_global
     by (simp add: assms(1) assms(2) assms(3) claim1_global) 
   define r::rat where "r = i - j"
   have r_gt_0: "r > 0" using i_gt_j r_def by simp
   have fi_gt_0: "(f i) > 0" using krat2[of i] i_gt_0 by simp
   have fr_gt_0: "(f r) > 0" using krat2[of r] r_gt_0 by simp
   have "f (j + r) \<ge> f (j) + f (r)" using assms(2)[of j r] i_gt_0 j_gt_0 r_def r_gt_0 by simp
   have "f (j) + f (r) > min (f j) (f r)" using krat2[of i] krat2[of j] i_gt_0 j_gt_0 by auto
   have "(f i) = (f (j+r))" using r_def by simp 
   then have "(f i) \<ge> (f j) + (f r)" using assms(2)[of j r]  by (simp add: j_gt_0 r_gt_0) 
   then have "(f j) + (f r) > (f j)"  using fr_gt_0 by linarith 
   then have tesis:"(f i) > (f j)" using \<open>f j + f r \<le> f i\<close> by linarith 
   show "(f i) > (f j)" using tesis by simp qed


(*here, we prove (f (x^n)) > (x^n) - 1. This is used later in some manipulations to later use limits *)

lemma floor_pzero_global:
 fixes f:: "rat \<Rightarrow> real"
  fixes x y a :: "rat"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
 
shows "\<And>x n. 1 < x \<Longrightarrow> 0 < n \<Longrightarrow> (real_of_rat( (x^n) - 1)) < f x ^ n" 
 proof - 
   fix x::"rat"
   assume x_gt_1: "x>1"
   fix n::"nat"
   assume n_gt_0: "n>0"
   have "(x^n) > 1" using x_gt_1 n_gt_0 by simp
   have h1: "\<lfloor>(x^n)\<rfloor> \<le> (f(rat_of_int\<lfloor>x^n\<rfloor>))" using claim1_global
     using Fract_of_int_eq One_rat_def \<open>1 < x ^ n\<close> le_floor_iff nless_le
     by (simp add: assms(1) assms(2) assms(3)) 
   have h2: " (f(rat_of_int\<lfloor>x^n\<rfloor>)) \<le>  (f(x^n)) " using  f_strict1_global floor_less_one of_int_0_less_iff of_int_floor_le order_less_trans
 \<open>1 < x ^ n\<close> antisym_conv2
     by (smt (verit) assms(1) assms(2) assms(3) order.asym) 
   have temp: "(\<And>x y. 0 < x \<and> 0 < y \<Longrightarrow> f (x * y) \<le> f x * f y) "  using assms(1) by blast 
   have temp1: "(\<And>x y. 0 < x \<and> 0 < y \<Longrightarrow> f x + f y \<le> f (x + y)) "  using assms(2) by blast 
   have temp2: " \<exists>a>1. f a = real_of_rat a" using assms(3) by blast
(*first, we have (f (floor (x^n))) \<le> (f (x^n))) using the strictly increasing property.
then, we have the floor of (x^n) \<le> (f (floor of )x^n), using the integers case, claim1.
Then, we have floor (x^n) > (x^n) - 1.
Together, we string up an inequality, (f (x^n)) \<ge> (f (floor of (x^n))) \<ge> (floor of (x^n)) > (x^n) - 1
We then use mgg to add   (f x)^n \<ge> (f (x^n)) at the top of the inequality.
Collapsing this, we have our thesis, (f x)^n > (x^n) - 1 *)    
   have h3: "(f (x^n)) \<le>  ((f x)^n) "
     using x_gt_1 n_gt_0 assms  krat2_global[of f x]  mgg[of f x n] 
     using claim1_global krat2_global of_int_less_1_iff order.strict_trans order_refl by auto
    
   have "(rat_of_int \<lfloor>x ^ n\<rfloor> ) > (x^n) - 1"
     by (simp add: floor_less_cancel) 
   show " (real_of_rat( (x^n) - 1)) < f x ^ n"  using h1 h2 h3
     by (smt (verit, del_insts) \<open>x ^ n - 1 < rat_of_int \<lfloor>x ^ n\<rfloor>\<close> of_rat_less of_rat_of_int_eq)
 qed 

subsection "Limit Lemmas"

lemma B: "filterlim (\<lambda>x::real. 1 / x) (nhds 0) at_top"
proof
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  have "\<forall>\<^sub>F x in at_top. x > 1 / \<epsilon>"
    by (rule eventually_gt_at_top)

  thus "\<forall>\<^sub>F (x::real) in at_top. dist (1 / x) 0 < \<epsilon>"
    using eventually_gt_at_top[of 0]
    by eventually_elim (use \<open>\<epsilon> > 0\<close> in \<open>auto simp: field_simps\<close>)
qed

(*next, we have a helper lemma for 
proving the limit of root n ( 1 - (1 / (x^n))) is 1.
Unfortunately, I wasn't able to complete that. 
Firstly, there is great difficulty in proving the limit of some function of two variables.
Second, the lemma libraries for limits has very little useful lemmas for proving limits involving roots.
Only the nth root of n, and the nth root of a constant, have useful lemmas in NthRoot, tendsto, or limits.
Namely, LIMSEQ_root and LIMSEQ_root_const in NthRoot.thy , nothing involving roots in Limits.thy,
and nothing in filter.thy
For future work, it may be possible to get around this, by proving various results about the root function, or 
using some more abstract lemmas to prove results about the derivatives of the root function. 
One might also be able to prove results about the limits by proving it in a topological context, and then somehow 
working against the various type errors that arise between functions of one argument (not including fixed values), and 
functions of more than one argument. 

Likely the most helpful strategy would be to instead prove that the limit of  ((f x)^n) 
is greater than the limit of ((x^n) - 1), as this might not involve roots, and is a fair bit simpler.
I did not use this strategy primarily because of sunken cost, and I assumed that there would be 
a fair amount of lemmas involving the limits of many types of basic operations. 
However, there are a few caveats to this strategy - f is not defined by anything other than its properties,
and both (f x)^n and (x^n) - 1 are unbounded. 

In general, limits proved the most difficult part of this formalization. The written proof for this problem
spans but a single page,  and the use of limits is only a single line. 

In Isabelle, limits are formalized as a function that takes a function from ('a \<Rightarrow> 'b), and
two filters, one on the domain and the other on the codomain.
One of the filters will be (nhds x), where x is the value that the function approaches,
and the other filter will be more general, usually at_top, which is a filter that I believe 
formalizes the notion of going to infinity. There are actually many, slightly different forms of limits,
each of them likely being equivalent, but not always providing an easy capability of switching between each form,
which greatly hampers sledgehammer.
These other forms of limits are the LIMSEQ form, for the limit of sequences (terms indexed by a natural number, which
is useful here), the tendsto form, which is readily interchangeable with the filterlim form, and a more topological form,
which uses eventually and sets to capture the notion of a limit.

In general, it seems that there are two ways one can prove statements regarding limits. The first is to 
use the lemmas prove results about smaller functions and building up to larger functions, and the
other is a classic epsilon or epsilon-delta proof.


 *)

lemma C:
  fixes x::rat
  assumes "x>1"
  shows  "filterlim (\<lambda>n::nat. (1/(real_of_rat x)^n)) (nhds 0) at_top" 
proof - 
 
  (* for proving Lemma C, I first tried to use results about smaller functions, and tried to work my way up from there.
I actually proved it for the limit of x as x goes to infinity, but later realized this was a mistake.
I tried to use the same steps in that proof, albiet slightly modified, to prove C.
Ultimately, I learned about the LIMSEQ form of limits, which could easily transfer to the
filterlim form, because it uses tendsto. 
I then proved an equivalence between two slightly different typed versions, one of which was able
to be used in a LIMSEQ lemma, LIMSEQ_divide_realpow_zero.
This allowed me to succinctly prove the lemma. 
For the next lemmas in the strategy of building upon limits of smaller functions, 
I used this as the basis, because it entirely depended on n, and asserted x as a fixed variable.
 *)
  have rerat_shift:"(\<lambda>n::nat. real_of_rat(1/x^n)) = (\<lambda>n::nat. (1/(real_of_rat x)^n)) "
    by (simp add: of_rat_divide of_rat_power)
  define x1::real where x1_prop: "x1 = real_of_rat x"
  then have "x1\<ge>1" using assms(1) x1_prop by auto
  have "(\<lambda>n::nat. real_of_rat(1/x^n)) \<longlonglongrightarrow> 0"
      using LIMSEQ_divide_realpow_zero[of x1  1] x1_prop rerat_shift assms by force 
  then show ?thesis
    by (simp add: rerat_shift)   qed

  

(*This is the lemma for the limit of the ultimate function I needed, unfortunately, it was on x, not n.
Unfortunately, I did not realize this at the time, but the nice lemmas in the library that allowed me to 
work with taking the nth root, did not work on functions that also depended on n. 
The general strategy was to prove the limit of 1/x, then prove the limit of (1/x)^n, 
then prove (1/x)^n = (1/x^n), then prove the limit of 1 - (1/(x^n)), then prove the limit for
root n (1 - (1/(x^n))).
Even though this strategy eventually worked, it was still difficult.
Namely, there were many pitfalls involving proving equivalences between lambda expressions, 
and also proving equivalence between lambda and non-lambda expressions.
Additionally, x must be a real, and not real_of_rat. I'm unsure if this would have worked well in the main proof,
because it might rely on properties of the reals that the properties of rationals do not have. Regardless, it did not work 
because the limit must be on n, not x.  *)

lemma bigLim:
  fixes n::nat
  assumes "n>0"
shows  "filterlim (\<lambda>x::real. root n (1 - (1 / x^n))) (nhds 1) at_top"
proof -
  let ?f0 =  "\<lambda>x::real. root n ( 1 - 1 / (x ^ n))"
  let ?f1 = "\<lambda>x::real. 1 - 1 / (x ^ n)"
  let ?f2 = "\<lambda>x::real.  1 / (x ^ n)"
  let ?f3 =  "\<lambda>x::real.  1 / x"
  have  "filterlim (\<lambda>x::real. (1 - (1 / x^n))) (nhds 1) at_top "
  proof -
      have h1: " (\<lambda>x::real. (1 / x^n)) = ((\<lambda>x. power_int (?f3 x) n))"  
        by (simp add: power_one_over)  
      have h2: "filterlim ?f3 (nhds 0) at_top" using B  by presburger
      then have h3: "((\<lambda>x. power_int (?f3 x) n) \<longlongrightarrow> power_int 0 n) at_top" 
        using of_nat_0_le_iff tendsto_power_int' by blast
      then have h4: "((\<lambda>x. (?f3 x)^ n) \<longlongrightarrow>  0^ n) at_top" by simp  
      then have h4a: "((\<lambda>x. (?f3 x)^ n) \<longlongrightarrow>  0) at_top" using assms(1)
        by (simp add: zero_power)
      then have h5: "?f2 =  ((\<lambda>x. (?f3 x)^ n))"
        by (simp add: power_one_over)
      then have h6: "filterlim ?f2 (nhds 0) at_top"
        by (simp add: h4a) 
      have h7: "filterlim (\<lambda>x::real. (1 / x^n)) (nhds 0) at_top " using h1 h2 h3 h4 h4a h5 h6 by auto
      then have "filterlim ?f2 (nhds 0) at_top" by simp
      have "?f1 =  (\<lambda>x. 1 - (?f2 x))" by simp
      then have "filterlim ?f1 (nhds 1) at_top" 
        using assms(1) tendsto_const tendsto_diff h7  by fastforce 
      then show ?thesis by simp  qed
      (*why was this so hard *)
      have "?f0 =  (\<lambda>x. root n (?f1 x))" by simp  
      then have  "filterlim ?f0 (nhds 1) at_top" using tendsto_real_root[of ?f0 1 at_top n ] real_root_one
        by (metis \<open>((\<lambda>x. 1 - 1 / x ^ n) \<longlongrightarrow> 1) at_top\<close> assms(1) tendsto_real_root)
 
    
      thus "((\<lambda>x. root n (1 - 1 / x ^ n)) \<longlongrightarrow> 1) at_top" by simp  qed 

(*like before, we prove a helper lemma before proving limits involving roots.
This one was fairly simple, and we are able to use C to proving things about (1/x^n)
Then, we take the entire function to be composed of the function 1 - var applied to
a function (f2 n). After combing the libaries, this became pretty simple. Unfortunately,
sledgehammer could not often find or use these lemmas, nor could it often solve it without 
explicitly introducing variables using "of" *)

lemma bigtinyhelper: 
  fixes x::"rat"
  assumes "x>1"
  shows  "filterlim (\<lambda>n::nat. 1 - ( 1 / ((real_of_rat x) ^ n))) (nhds 1) at_top"
proof -
 let ?f0 =  "\<lambda>n::nat. root n ( 1 - 1 / ((real_of_rat x) ^ n))"
  let ?f1 = "\<lambda>n::nat. 1 - ( 1 / ((real_of_rat x) ^ n))"
  let ?f1a = "\<lambda>n. 1"
  let ?f2 = "\<lambda>n::nat.  1 / ((real_of_rat x) ^ n)"
  have "?f1 = ?f1a - ?f2" by auto
  have "filterlim (\<lambda>n::nat.  1 / ((real_of_rat x) ^ n)) (nhds 0) at_top" using C[of x] assms by auto 
  then have "filterlim ?f1 (nhds 1) at_top" using  tendsto_const[of 1]
      tendsto_diff[of ?f1a 1 at_top  ?f2 0 ] by simp
  then show ?thesis by auto  qed


(*unfortunately, this did not prove. I did not realize it, but there were no lemmas 
regarding taking a root n of a function that was dependent on n. *)
lemma bigLimN_not_X:
  fixes x::"rat"
  assumes "x>1"
shows  "filterlim (\<lambda>n::nat. root n (1 - (1 / ((real_of_rat x)^n)))) (nhds 1) at_top"
proof -
  let ?f0 =  "\<lambda>n::nat. root n ( 1 - 1 / ((real_of_rat x) ^ n))"
  let ?f1 = "\<lambda>n::nat. 1 - ( 1 / ((real_of_rat x) ^ n))"
  have "filterlim ?f1 (nhds 1) at_top" using bigtinyhelper[of x] assms by auto
  have "\<forall>x::rat. x>0 \<longrightarrow> (\<forall>n::nat. (1/(x^n))>0)" by simp

  show "filterlim ?f0 (nhds 1) at_top"  sorry qed


(*Being that that failed, I tried to use copy and modify an epsilon proof from Sage on a linear sequence
One of the helper lemmas involved the sequence being an increasing sequence.
Sledgehammer was able to prove this, but it was very difficult for it.  *)

(*for this lemma, I prove that the linear sequence is increasing, which is necessary in 
an epsilon-delta proof. It is fairly straightforward
 *)

lemma rootnf_inc:
  fixes x::"rat"
  assumes "x>1"
  fixes A
  assumes "A =  (\<lambda>n::nat. root n (1 - (1 / ((real_of_rat x)^n))))"
  shows "\<And>m n. n \<le> m \<Longrightarrow> A n \<le> A m"
proof -
  fix m n::nat
  assume "m \<ge> n"
  have "1 - (1/((x)^n)) \<le> 1 - (1/((x)^m))" 
    by (metis (mono_tags, lifting) \<open>n \<le> m\<close> assms(1) diff_left_mono divide_less_eq_1_pos dual_order.strict_trans2 
linordered_nonzero_semiring_class.zero_le_one power_decreasing_iff
 power_one_over zero_less_divide_1_iff)

  then have "1 - (1/((real_of_rat x)^n)) \<le> 1 - (1/((real_of_rat x)^m))" 
    by (metis (mono_tags, opaque_lifting) of_rat_1 of_rat_diff of_rat_divide of_rat_less_eq of_rat_power) 
  have "root n (1 - (1/((real_of_rat x)^n))) \<le> root m ( 1 - (1/((real_of_rat x)^m)))"
    by (smt (verit, ccfv_SIG) \<open>1 - 1 / real_of_rat x ^ n \<le> 1 - 1 / real_of_rat x ^ m\<close> \<open>n \<le> m\<close> assms(1)
 divide_le_eq_1_pos eq_iff_diff_eq_0 le_divide_eq_1_pos one_less_of_rat_iff
 power_le_one_iff power_less1_D power_strict_increasing_iff real_root_increasing real_root_le_mono real_root_zero zero_less_divide_1_iff) 
  then show " A n \<le> A m" using assms(2) by auto  qed

(*Here I attempt an epsilon proof of the limit of the linear sequence A.
We prove that by trying to prove there exists some point N where forall points greater than or equal to it, 
the distance between that term and the limit is less than epsilon. *)
lemma B1:
  fixes x::rat
  assumes "x>1"
shows "filterlim (\<lambda>n::nat. root n (1 - (1 / ((real_of_rat x)^n)))) (nhds 1) at_top"
proof -
  define A where a_def: " A = (\<lambda>n::nat. root n (1 - (1 / ((real_of_rat x)^n))))"
  have "\<forall>\<epsilon> > 0. \<exists>N. \<forall>n \<ge> N. \<bar>A n - 1\<bar> < \<epsilon>"
  proof clarify
    fix \<epsilon> :: real
    assume *: "\<epsilon> > 0"
    obtain N::nat where "\<forall>n \<ge> N. \<bar>A n - 1\<bar> < \<epsilon>"
      proof -
        obtain N::nat where N: "root N  (1 - (1 / ((real_of_rat x)^N))) < \<epsilon>"
          by (metis "*" root_0)
(*         proof -
          obtain N::nat where "N = 1" by auto
          have "  (1 / ((real_of_rat x)^1)) < 1"
            using assms by auto
          then have "( 1 - (1/((real_of_rat x)^1))) < 1"
            using assms by auto
          then have "( 1 - (1/((real_of_rat x)^1))) > 0" using B
            using \<open>1 / real_of_rat x ^ 1 < 1\<close> by auto
*)
(*
Unfortunately, this did not work. There are only two lemmas involving roots and limits of sequences,
namely, LIMSEQ_root and LIMSEQ_root_const. These only apply to the nth root of n, and the nth root of a constant.
Unfortunately, induct on c and have c be the output of our function, because our function depends on n. 
It doesn't seem possible to have our function depend on x, because those limits are simply of different functions.

It may be possible to prove an epsilon proof regarding this, as I don't have much familiarity with it.
However, I'm not sure it's easier than other approaches. Likely, it would be easier
to prove that (f x)^n \<ge> (x^n) - 1 using limits, even if they are unbounded, and compare each term in the linear sequence.

 *)


        then have " \<forall>n \<ge> N. \<bar>A n - 1\<bar> < \<epsilon>"
           proof clarify
        fix n :: nat
        assume "N \<le> n"
        then have "A N \<le> A n" using rootnf_inc real_root_increasing
          by (simp add: a_def assms) 
        moreover have "\<bar>A N - 1\<bar> < \<epsilon>"
        proof - 
           have "root n ( 1 - (1/((real_of_rat x)^n))) < \<epsilon>" sorry
          show ?thesis sorry qed
          
        thus "\<bar>A n - 1\<bar> < \<epsilon>"   sorry qed
        then show ?thesis sorry qed
    show  "\<exists>N. \<forall>n \<ge> N. \<bar>A n - 1\<bar> < \<epsilon>"  sorry qed 
  then have "A \<longlonglongrightarrow> 1" using LIMSEQ_iff  by force
  show "filterlim (\<lambda>n::nat. root n (1 - (1 / ((real_of_rat x)^n)))) (nhds 1) at_top"
    using \<open>A \<longlonglongrightarrow> 1\<close> a_def by auto  
qed




      
(*we prove a short helper lemma converting between (x^n) and (x powi n).
When having trouble proving some result involving (x^n), I thought that
making it more general might solve the problem. It seemed to, at least temporarily,
but it's unlikely it's actually necessary, especially after some various reformatting 
changed many instances of powi to regular exponentiation using naturals. *)

lemma helper_2:
fixes x::"rat"
fixes n::"nat"
assumes "x>1" "n\<ge>1"
shows "(x^n = x powi n) \<and> ( (real_of_rat x)^n) = ((real_of_rat x) powi n)"
proof -  show ?thesis by simp qed

(*Then we prove another helper lemma, used in
algebraic manipulation for proving (f x) \<ge> x forall x>1.
Unfortunately, even that simple algebraic manipulation is actually rather difficult. Compounding this was
the fact that for a few days (and some dozen of work-hours, Sledgehammer was very limited in its memory usage,
using or being able to use only a quarter of the memory it normally uses.  *)

lemma helper_1:
  fixes x y :: "rat"
  fixes n :: "nat"
  assumes "x>0" 
  "n \<ge> 1"
shows "(root n (real_of_rat(x^n - 1))) = ( (real_of_rat x) * (root n  (real_of_rat(1 - 1 / (x^n)))))"
proof - 
(*We prove this by manipulation (x^n) - 1 into ((x^n)*(1 - (1/(x^n)))), by dividing both sides by (x^n)
Then, we take the nth root of both sides. 
Then, we can take the x out of the RHS. Later in the (f x)\<ge>x for x>1 case, we divide (f x) by x,
isolating what I hoped would be the easiest root to take. After all, this made the RHS bounded by 1. *)
  have "(real_of_rat((x^n) - 1)) = real_of_rat(x^n) *  (real_of_rat(1 - 1 / (x^n)))" 
    by (smt (verit, del_insts) assms(1) diff_divide_distrib divide_less_cancel divide_self_if nonzero_mult_div_cancel_left nonzero_of_rat_divide zero_eq_of_rat_iff zero_less_power)
  then have "(root n (real_of_rat(x^n - 1))) = (root n ( real_of_rat(x^n) *  (real_of_rat(1 - 1 / (x^n)))))" by auto
  have "(root n  (real_of_rat (x*y))) = (root n (real_of_rat x)) * (root n (real_of_rat y))"
    by (simp add: of_rat_mult real_root_mult)
  define xn::rat where xn_def: "xn = (x^n)"
  define x1::real where x1_def: "x1 = real_of_rat x"
  have "root n (real_of_rat (x ^ n)) = real_of_rat x" using root_sgn_power[of n x1] assms(2)
    by (simp add: assms(1) of_rat_power real_root_pow_pos real_root_power)
  (*above statement took sledgehammer over 30 seconds to prove *)
   then show ?thesis
     by (simp add: \<open>real_of_rat (x ^ n - 1) = real_of_rat (x ^ n) * real_of_rat (1 - 1 / x ^ n)\<close> real_root_mult)
 qed

(*suprisingly, this helper lemma is actually used. For many later proofs, sledgehammer
reached the end of its capabilities, with the amount of large lemma libraries, and large amount of variables.
This could have been remedied by proving lemmas as have statements inside of f_is_identity, which would
eliminate the need to use the assumptions of f_is_identity each time one wanted to use those helper lemmas. *)
lemma helper_3:
  fixes x::"real"
  fixes n::"nat"
  assumes "n\<ge>1"
 assumes "x\<ge>0" 
  shows "n\<ge>1 \<Longrightarrow> root n (x powi n) = x "
proof - 
  show ?thesis using real_root_power_cancel
    using assms(1) assms(2) by auto qed



(*helperlimextra is unused *)
lemma helperlimextra:
  fixes f:: "rat \<Rightarrow> real"
  fixes x y a :: "rat"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a" 
  "x>1"

shows "\<forall>n.  (f x) / (real_of_rat x) \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))"
proof - 
    have sploinky: "\<And>x. 1 < x \<Longrightarrow>(real_of_rat  x) \<le> (f x)"
  proof -
    fix x::"rat"
    fix n::"nat"
    assume x_gt_1: "x>1"
(*finally fucking got this at least. now try and do rooting. *)
    show "(real_of_rat  x) \<le> (f x)" proof -
      have h_a:"(f x) powi n > (real_of_rat ((x powi n) - 1))"
      proof -
        have h0: "n>0 \<or> n=0" by auto
        have h1: "n>0 \<Longrightarrow> (f x) powi n > (real_of_rat ((x powi n) - 1))" using floor_pzero_global[of f x n]
 x_gt_1
          by (simp add: assms(1) assms(2) assms(3)) 
        have h2: "n=0 \<Longrightarrow> (f x) powi n > (real_of_rat ((x powi n) - 1))" 
        proof -
          assume n_eq_0: "n=0"
          have g1:"(f x) ^ n = 1" using n_eq_0 by auto
          then have g2:"(real_of_rat ((x powi n) - 1)) = 0" using n_eq_0 by auto

          then show ?thesis using g1 g2 by simp qed
        
        show ?thesis using h0 h1 h2 by auto qed

(*note that for some reason it only works for \<ge>. SO IT'S WEAKER HERE.*)
      have " n = 0 \<Longrightarrow> (f x) powi  n \<ge> (real_of_rat x powi n) " by simp
      have " n \<ge> 1 \<Longrightarrow> (f x) powi n \<ge> (real_of_rat x powi n)" 
       sorry (*
        assume n_gte_1: "n\<ge>1"
      have "(root n ((f x) powi n)) \<ge> root n (real_of_rat ((x powi n) - 1))" using h_a 
        by (metis less_eq_real_def not_gr_zero real_root_le_iff root_0)
      define sploinkyfx::"real" where sfx_def: "sploinkyfx = (f x)" 
      then have "(f x) \<ge>  root n (real_of_rat ((x ^ n) - 1))" using helper_3[of n sploinkyfx] sfx_def krat2_global
        by (smt (verit, ccfv_threshold) \<open>root n (real_of_rat (x powi int n - 1)) \<le> root n (f x powi int n)\<close> a_prop assms(1) assms(2) claim1 n_gte_1 one_less_of_rat_iff power_int_of_nat x_gt_1 zero_less_of_rat_iff)
     then have "(f x) \<ge>  root n (real_of_rat ((x powi n) - 1))"  using helper_3[of n sploinkyfx] sfx_def krat2_global by simp

      have "(root n (real_of_rat(x^n - 1))) = ( (real_of_rat x) * (root n  (real_of_rat(1 - 1 / (x^n)))))" 
        using helper_1[of x n] n_gte_1 x_gt_1  by linarith 
      then have before_lims: "root n (real_of_rat ((x powi n) - 1)) = (real_of_rat x) * root n (real_of_rat (1 - (1/(x^n))))"
        using helper_2  by simp 
      then have before_lims2: "(f x) / (real_of_rat x) \<ge>  root n (real_of_rat (1 - (1/(x^n))))"
        by (smt (verit) \<open>root n (real_of_rat (x ^ n - 1)) = real_of_rat x * root n (real_of_rat (1 - 1 / x ^ n))\<close> \<open>root n (real_of_rat (x ^ n - 1)) \<le> f x\<close> divide_le_cancel nonzero_mult_div_cancel_left one_less_of_rat_iff x_gt_1) 
      then have before_lims3:  "(f x) / (real_of_rat x) \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))"  by (simp add: of_rat_diff of_rat_divide of_rat_power)sorry
   *)  show ?thesis sorry qed qed show ?thesis  sorry qed



(*Unfortunately, wasn't able to prove this. 
Tendsto_le seems like a very useful lemma here, but unfortunately, it requires assuming
(f n) \<ge> (g n) forall n. Unfortunately, we can't just break off the assumption without fixing the variables,
and fixing the variables forbids that proof. 
Not only that, but we would need to prove an eventually statement, which might be possible using
LIMSEQ lemmas, but isn't able to be proved outright using sledgehammer.
I believe the lemma is correct, though, because even though it doesn't state it in the form of a LIMSEQ,
we still know that there is an N where for each n afterwards, (f n) \<ge> (g n), using
the definition of the limit. This should be easy to coax out of the definition for filterlim.
One curiosity is that the necessary precondition "at_top \<noteq> bot" is not proved by sledgehammer.
Hopefully, this could be proved by proving that f and g are monotonic. 
However, that would need to be added as an assumption. 
Regardless, the following lemma is absolutely necessary for being able to apply the limits of the function 
and say that if the limit of the RHS is some number, and the LHS is greater than that number,
then the LHS is greater than the RHS.
 *)

lemma testLHSRHS: 
  fixes f g::"('a::order) \<Rightarrow> real"
  assumes lim1:"filterlim f (nhds a) at_top"
  assumes lim2: "filterlim g (nhds b) at_top"
shows "\<And>n. g n \<le> f n \<Longrightarrow> b \<le> a"
proof -
  fix n
  assume "(f n) \<ge> (g n)" 
  have  "eventually (\<lambda>n. g n \<le> f n) at_top" using assms  sorry
(*One should be able to prove this somehow, by somehow converting the fixed n into a 
forall statement, and then using a LIMSEQ definition. *)
  then have "\<forall>\<^sub>F x in at_top. g x \<le> f x" by simp
  have "at_top \<noteq> bot"  sorry
(*curiously, this did not prove by sledgehammer.  *)
  thus  "a\<ge>b" using tendsto_le [of at_top f a g b ] assms
    using \<open>\<forall>\<^sub>F x in at_top. g x \<le> f x\<close> by auto
     qed

lemma helperLimLHSRHS:
  fixes f g::"('a::order) \<Rightarrow> real"
  assumes lim1:"filterlim f (nhds a) at_top"
  assumes lim2: "filterlim g (nhds b) at_top"
shows "\<forall>n. (f n) \<ge> (g n) \<longrightarrow> a  \<ge> b" 
proof -
  show ?thesis using testLHSRHS (*is sorried *)
    using lim1 lim2 by blast
    qed

section "Main Theorem"

lemma f_is_identity:
  fixes f:: "rat \<Rightarrow> real"
  fixes x y a :: "rat"
  assumes 
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> (f x) *  (f y) \<ge> f (x * y)"
  "\<And>x y::rat. x > 0 \<and> y > 0 \<Longrightarrow> f (x + y) \<ge> f x + f y"
  "\<exists>a::rat. a > 1 \<and> f a = (real_of_rat) a"  
shows "\<And>x::rat. x > 0 \<Longrightarrow> f x = (real_of_rat) x"
proof -
  obtain a::"rat" where a_prop: "a > 1 \<and> f a = (real_of_rat) a" using assms(3) by auto
 have claim1: " \<And>n. 0 < n \<Longrightarrow> real_of_int n \<le> f (rat_of_int n)" using claim1_global

   using a_prop assms(1) assms(2) by auto

     (* have f_strict: "\<forall>i j::rat. i>0 \<and> i>j \<longrightarrow> (f i) > (f j)" *)
  have f_strict1: " \<And>i j. 0 < i \<Longrightarrow> 0 < j \<Longrightarrow> j < i \<Longrightarrow> f j < f i" 
    using f_strict1_global a_prop assms(1) assms(2) by auto
  have mult_gen: "\<And>x n. 0 < x \<Longrightarrow> 0 < n \<Longrightarrow> f (x ^ n) \<le> f x ^ n" using mgg
    using a_prop assms(1) assms(2) claim1 krat2_global by auto

  (*This lemma is used in the proof of (f x) \<le> x for x>1 case. a is a fixed point, and *)
   have fan: "\<And>n. 0 < n \<Longrightarrow> \<exists>a. 1 < a \<and> f a = real_of_rat a \<Longrightarrow> f (a ^ n) \<le> real_of_rat a ^ n"
        proof -
          fix n::"nat"
          assume n_gt_0: "n>0"
          show " \<exists>a. 1 < a \<and> f a = real_of_rat a \<Longrightarrow> f (a ^ n) \<le> real_of_rat a ^ n"
          proof -
            assume " \<exists>a. 1 < a \<and> f a = real_of_rat a"
            show " f (a ^ n) \<le> real_of_rat a ^ n" 
            proof -
              have "n>0" using n_gt_0 by auto
              then have nz: " n>0 \<Longrightarrow>  f (a ^ n) \<le> real_of_rat a ^ n"
                proof (induct n)
                  case 0
                  then show ?case by simp  
                next
                  case (Suc n)
                  have "(a ^ (Suc n)) = (a ^ n) * a" by simp
                  then have "f(a ^ (Suc n)) = f ((a ^ n) * a)" by presburger
                  then have "f (a ^( Suc n)) \<le> (f a) * (f (a^n))" using assms(1)
                    by (metis a_prop div_by_0 divide_less_eq_1 mult.commute order.strict_trans zero_less_power)
                  

                  then show ?case using a_prop
                    by (metis dual_order.strict_trans2 linordered_nonzero_semiring_class.zero_le_one mult_gen zero_less_Suc)
                qed 
              show ?thesis using nz n_gt_0 by auto qed qed qed
 have fan2: "\<And>n. 0 < n \<Longrightarrow> f (a ^ n) \<le> real_of_rat (a ^ n)" using fan assms(3)
        by (simp add: of_rat_power)   
 have fan3:  "\<And>n. 0 < n \<Longrightarrow>   \<lfloor>a ^ n\<rfloor>  \<le>  f (a ^ n)"
    proof - 
    fix n::"nat"
    assume n_gt_0: "n>0"   
    have "(a^n) > 1" using a_prop n_gt_0 by simp
    have h1: "\<lfloor>(a^n)\<rfloor> \<le> (f(rat_of_int\<lfloor>a^n\<rfloor>))" using claim1
      using Fract_of_int_eq One_rat_def \<open>1 < a ^ n\<close> le_floor_iff nless_le by auto
    have h2: " (f(rat_of_int\<lfloor>a^n\<rfloor>)) \<le>  (f(a^n)) "
      by (smt (verit, del_insts) \<open>1 < a ^ n\<close> antisym_conv2 f_strict1 floor_less_one of_int_0_less_iff of_int_floor_le order_less_trans)
    then show " \<lfloor>a ^ n\<rfloor>  \<le>  f (a ^ n)" using h1 h2 by simp  qed


  have floor_p0:"\<And>x n. 1 < x \<Longrightarrow> 0 < n \<Longrightarrow> (real_of_rat( (x^n) - 1)) < f x ^ n" 
    using floor_pzero_global using assms by auto

(*For this one, we fix vars, and use earlier helper lemmas to prove the initial inequality.
Then, we algebraically manipulate the RHS into the desired form.  *)
  have foralln_inequality: "\<And>x. \<And>n. 1 < x \<Longrightarrow> 0 < n \<Longrightarrow> (f x) / (real_of_rat x) \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))"
  proof -
    fix n::"nat"
    fix x:: "rat"
    assume n_gt_0: "0 < n" 
    assume x_gt_1: "x>1"
    show "(f x) / (real_of_rat x) \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))" 
    proof -
      have h_a:"(f x) powi n > (real_of_rat ((x powi n) - 1))"
        by (simp add: floor_p0 n_gt_0 x_gt_1)

      have "(f x) / (real_of_rat x) \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))" 
      proof - 
      have h_something:"(root n ((f x) powi n)) \<ge> root n (real_of_rat ((x powi n) - 1))" using h_a 
        by (metis less_eq_real_def not_gr_zero real_root_le_iff root_0)
      define sploinkyfx::"real" where sfx_def: "sploinkyfx = (f x)" 
      then have "(f x) \<ge>  root n (real_of_rat ((x ^ n) - 1))" using helper_3[of n sploinkyfx] sfx_def h_something  krat2_global a_prop assms(1) assms(2) claim1_global n_gt_0 x_gt_1
        by (smt (z3) diff_gt_0_iff_gt floor_p0 helper_3 less_one nat_less_real_le of_nat_0 of_nat_1 of_nat_le_iff power_int_of_nat power_one_right power_one_right zero_less_of_rat_iff)
      then have "(f x) \<ge>  root n (real_of_rat ((x powi n) - 1))"  using helper_3[of n sploinkyfx] sfx_def krat2_global by simp
      have "(root n (real_of_rat(x^n - 1))) = ( (real_of_rat x) * (root n  (real_of_rat(1 - 1 / (x^n)))))" 
        using helper_1[of x n] n_gt_0 x_gt_1  by linarith 
      then have before_lims: "root n (real_of_rat ((x powi n) - 1)) = (real_of_rat x) * root n (real_of_rat (1 - (1/(x^n))))"
        using helper_2  by simp 
      then have before_lims2: "(f x) / (real_of_rat x) \<ge>  root n (real_of_rat (1 - (1/(x^n))))"
        by (smt (verit) \<open>root n (real_of_rat (x ^ n - 1)) = real_of_rat x * root n (real_of_rat (1 - 1 / x ^ n))\<close> \<open>root n (real_of_rat (x ^ n - 1)) \<le> f x\<close> divide_le_cancel nonzero_mult_div_cancel_left one_less_of_rat_iff x_gt_1) 
      then have before_lims3:  "(f x) / (real_of_rat x) \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))"
        by (simp add: of_rat_diff of_rat_divide of_rat_power)
      then show ?thesis
        by auto
    qed
    then show ?thesis by blast
  qed qed

(*
    (* Want to take the limit of both sides wrt n.  LHS is constant wrt n. *)
      obtain k:: "real" where k_prop: "(f x) / (real_of_rat x) = k"
        by blast

      have "k \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))"
        using foralln_inequality n_gt_0 k_prop by auto

      have "filterlim (\<lambda>n. k) (nhds k) at_top"
        by blast

      then have "filterlim (\<lambda>n. (f x) / (real_of_rat x)) (nhds ((f x) / (real_of_rat x))) at_top"
        using k_prop by auto

      have "filterlim (\<lambda>n. root n ( (1 - (1/((real_of_rat x)^n))))) (nhds 1) at_top"
        (* helper lemma *) using bigLim
        sorry
*)
  
  have sploinky: "\<And>x.  1 < x  \<Longrightarrow> (real_of_rat  x) \<le> (f x)" 
  proof -


    fix x::"rat"
    assume x_gt_1: "x>1"
   (* assume n_gte_1: "n\<ge>1" *)
(*finally fucking got this at least. now try and do rooting. *)
    show "(real_of_rat  x) \<le> (f x)"   proof -
      obtain k:: "real" where k_prop: "(f x) / (real_of_rat x) = k" by blast
(*i hope this n is alright *)
      obtain n::"nat" where n_prop: "n>0" by blast
      let ?lhs = "\<lambda>x.(f x) / (real_of_rat x) "
      let ?rhs = "\<lambda>x. root n ( (1 - (1/((real_of_rat x)^n)))) "
      have k_gt:"k \<ge>  root n ( (1 - (1/((real_of_rat x)^n))))"
        using foralln_inequality n_prop k_prop x_gt_1 by auto 
      have const_lim:"filterlim (\<lambda>n. k) (nhds k) at_top" by blast
      then have cl_sub: "filterlim (\<lambda>n. (f x) / (real_of_rat x)) (nhds ((f x) / (real_of_rat x))) at_top"
        using k_prop by auto                 
      have rhs_lim:"filterlim (\<lambda>n. root n ( (1 - (1/((real_of_rat x)^n))))) (nhds 1) at_top"
        (* helper lemma *) using bigLimN_not_X[of x] n_prop x_gt_1 by auto 
      have "(f x) / (real_of_rat x) \<ge> 1 " using k_gt const_lim cl_sub
          rhs_lim helperLimLHSRHS[of ?lhs k ?rhs 1]  using helperLimLHSRHS k_prop by blast
      thus  ?thesis
        using x_gt_1 by auto 
    qed qed

 have fan4: "\<And>n. 0 < n \<Longrightarrow> \<exists>a. 1 < a \<and> f a = real_of_rat a \<Longrightarrow> f (a ^ n) \<ge> real_of_rat a ^ n"
 proof -
   fix n::"nat"
   assume n_gt_0: "n>0"
   show " \<exists>a. 1 < a \<and> f a = real_of_rat a \<Longrightarrow> f (a ^ n) \<ge>  real_of_rat a ^ n" 
   proof -
     assume " \<exists>a. 1 < a \<and> f a = real_of_rat a"
     show " f (a ^ n) \<ge> real_of_rat a ^ n" 
     proof -
       have "n\<ge>0" using n_gt_0 by simp
       then have "(a^n) \<ge> 1" using a_prop by simp 
       have  "n>0" using n_gt_0 by auto
       then have nz: " n>0 \<Longrightarrow>  f (a ^ n) \<ge> real_of_rat a ^ n" using sploinky
         by (metis a_prop of_rat_power one_less_power)
    show ?thesis using nz n_gt_0 by auto qed qed qed



(*maybe need to change to 1 \<le> x *)
  have sploinky2: "\<And>x. 1 < x \<Longrightarrow>(real_of_rat  x) \<ge> (f x)"
  proof -
    fix x::"rat"
    fix n::"nat"
    assume x_gt_1: "x>1"
(*finally fucking got this at least. now try and do rooting. *)
    show "(real_of_rat  x) \<ge> (f x)"
    proof -
(*Here, the lemma sowry might necessitate another proof by limits, as the corresponding proof
takes n to be arbitarily large. This is because x, while fixed, is simply any value greater than 1, so 
one would have to prove for any valid value of x, there exists an m satisfying the condition. 
Proving limits in isabelle is more difficult than it might seem.  *)
      have sowry: "\<exists>m::nat. (f ((a^m) - x)) > 0 \<and> ((a^m) - x) > 1 " sorry
      then obtain m::nat where m_prop: " (f ((a^m) - x)) > 0 \<and>  ((a^m) - x) > 1  " by auto
      define ammx::rat where am_def: "ammx = (a^m) - x" 
      have "ammx >0" using m_prop sowry am_def by simp
      have h1:" (f ((a^m))) \<ge> (f ((a^m) - x)) + (f x)" using assms(2)[of ammx x]
        using \<open>0 < ammx\<close> am_def x_gt_1 by auto 
      have h2:"(f ((a^m) - x)) + (f x) \<ge> real_of_rat ((a^m - x) + x)" using sploinky
        by (metis add_mono m_prop of_rat_add x_gt_1)
      have "(f (a^m)) = (real_of_rat(a^m))"
        by (smt (verit) \<open>0 < ammx\<close> a_prop am_def diff_eq_eq fan2 pos_add_strict power_0 power_strict_increasing_iff sploinky x_gt_1)
      then have "(f x) \<le> (real_of_rat ((a^m) - ((a^m)-x))) "
        by (smt (verit, best) h1 m_prop of_rat_diff sploinky)
      then have "(f x) \<le> real_of_rat x"
        by simp
      then show ?thesis by simp qed qed

 (*Therefore, we have $f(x)=x$ for all rationals $x>1$. We see that $2=f(2)\ge 2f(1)$,
 so $f(1)\le 1$, but we know $f(1)\ge 1$, so $f(1)=1$ as well.
 Then, (i) gives $f(1/x)\ge 1/f(x)$. But we know $f(x)\le x$, so we get $f(1/x)\ge 1/x$.
 We already know from before that $f(1/x)\le 1/x$, so we have $f(1/x)=1/x$ for all rationals $x>1$.
 This shows that $f(x)=x$ for all positive rationals $x$, completing the solution. *)
  have sploinky3:  "\<And>x. 1 < x \<Longrightarrow>(real_of_rat  x) = (f x)" using sploinky sploinky2 by fastforce 

  have f1case: "(f 1) = 1"
  proof -
(*we've proved for all integers n, (f n) \<ge> n.
here, we only prove it for (f 1) = 1.
We know (f 2) = 2 from the x>1 case.  (f 2) \<ge> (f 1) + (f 1) by assumption 2,
and so (f 2) = 2*(f1).
we know n(f x) \<le> f (n x) by the sublinear lemma, so we substitute 2 in, 
and we get 2*(f 1) \<le> (f 2). Dividing by two on both sides, (f 1) \<le> 1.
Combining this and the integers case, we find that (f 1) = 1.
 *)

    have ftwotwo: "(f 2) = 2" using sploinky3[of 2] by simp
    have "(f 2) \<ge> (f 1) + (f 1) " using assms(2)[of 1 1] by simp
    then have "(f 2) \<ge> 2 * (f 1)" by simp
    then have f1_lt: "(f 1) \<le> 1" using sublinear[of f 1 2] f_strict1 assms(1) ftwotwo by linarith
      then have " f (a * 1) = real_of_rat a" using a_prop  assms(1)[of a 1] using sublinear by auto
      then have "real_of_rat a * (f 1) \<ge> real_of_rat a" using a_prop assms(1)[of a 1] by simp
      then have f1_gt:  "f 1 \<ge> 1" using a_prop mult_cancel_left1 by auto  
    then show ?thesis using f1_lt f1_gt by auto qed
(*now we must prove, that forall x between 1 and 0, (f x) = x. 
we do not need to prove it for x = 1, because identity for integers is already proved. 
We divide it into (f x) \<ge> x, and (f x) \<le> x
 *)
  have caseInterval: "\<And>x. x < 1 \<Longrightarrow> 0 < x \<Longrightarrow> real_of_rat x \<le> f x" 
  proof - 

(*
Here, we first prove a helperlemma, for x>1, we prove that (f x) * (f (1/x)) \<ge> (f 1), using assms 1, 
then, because we've proved identity for 1, we prove that (f x) * (f (1/x)) / (f x) \<ge> 1/(f x)
then, becuase x>1, we can say that (f (1/x)) \<ge> 1/x.
 *)
    have caseIntervalHelper: "\<And>x. x > 1 \<Longrightarrow> real_of_rat (1/x) \<le> f (1/x)" 
      proof - 
        fix x::rat
        assume x_gt_1: "x>1"
        have overx_gt_0: "(1/x) < 1" using  x_gt_1  by force
        then have overx_gt_1: "(1/x) > 0" using x_gt_1 by force
    define overx::rat where overx_def: "overx = (1/x)"
    have "(f x) * (f (1/x)) \<ge> (f 1)" using assms(1)[of x overx] using overx_def overx_gt_1 by force 
    then have "(f x) * (f overx) \<ge>  1" using claim1[of 1] assms(1) overx_def by simp
    then have "(f x) * (f (1/x)) \<ge> 1"  using overx_def by auto 
    then have "((f x) /(f x)) * (f (1/x)) \<ge> (1/ (real_of_rat x))"
      by (metis comm_monoid_mult_class.mult_1 divide_self dual_order.irrefl mult.commute mult_imp_div_pos_le overx_gt_1 sploinky3 x_gt_1 zero_less_divide_1_iff zero_less_of_rat_iff)
    then have "(f (1/x)) \<ge> real_of_rat (1/x)" using sploinky3[of x] using overx_gt_0 sploinky3
      by (metis divide_eq_0_iff divide_eq_1_iff mult.commute mult.right_neutral of_rat_1 of_rat_divide order_refl x_gt_1)
    then show  "real_of_rat (1/x) \<le> f (1/x) " by auto qed

  fix x::"rat" 
  assume x_gt_0: "x>0"
  assume x_lt_1: "x<1"
  define xover::"rat" where "xover = (1/x)"
  then have "xover > 1" using x_gt_0 x_lt_1 by auto 

  then show "real_of_rat x \<le> f x" using caseIntervalHelper[of xover]
    by (simp add: xover_def)  qed

  have caseInterval2:  "\<And>x. x < 1 \<Longrightarrow> 0 < x \<Longrightarrow> real_of_rat x \<ge> f x" 
  proof - 

(*for this proof, it's important to not try to use the book, and prove that for x<1, then 
f (1/x) \<le> (1/x). It's probably possible, but using quantifiers allows you to use it as a helper lemma, which makes it easier
Originally, I tried to prove it using the first strategy, but it was even difficult to prove some equivalent of 
"tassms", upon which hinged all of caseInterval2.  *)
      have tassms:" \<And>x1. x1 < 1 \<Longrightarrow> 0 < x1 \<Longrightarrow> \<exists>m2::rat. m2 > 1 \<and> m2 - rat_of_int \<lfloor>m2\<rfloor>  = x1"
      proof - 
        fix x1::rat
        assume x1_gt_0: "x1>0"
        assume x1_lt_1: "x1<1"

        show "\<exists>m2::rat. m2 > 1 \<and> m2 - rat_of_int \<lfloor>m2\<rfloor>  = x1" proof -
          obtain m2::rat where m2_prop: "m2 > 1 \<and> m2 - rat_of_int \<lfloor>m2\<rfloor>  = x1"
          proof - 
            obtain m2::rat where m2a_prop: "m2 = x1+1" by auto
            have "m2 = x1 + 1 \<Longrightarrow> m2 > 1 \<and> m2 - rat_of_int \<lfloor>m2\<rfloor>  = x1"
              by (metis add_diff_cancel_right' diff_gt_0_iff_gt frac_1_eq frac_def frac_eq order_less_imp_not_less verit_comp_simplify1(3) x1_gt_0 x1_lt_1)
            show ?thesis sorry qed
          show ?thesis sorry qed qed
      have caseInterval2Helper:"\<And>x1. 0 < x1 \<Longrightarrow> x1 < 1 \<Longrightarrow> f x1 \<le> real_of_rat x1" proof -
        fix x1::"rat"
        assume x1_gt_0: "x1 > 0"
        show "x1 < 1  \<Longrightarrow>f x1 \<le> real_of_rat x1"
        proof -
          assume x1_lt_1: "x1 < 1"
          have x1_bt_01: "x1 > 0 \<and> x1 < 1"
            by (simp add: x1_gt_0 x1_lt_1)
        define x::rat where x_prop: "x = (1/x1)"
        have x_gt_1: "x>1"
          by (simp add: x1_bt_01 x_prop)
        have "\<exists>m2::rat. m2 > 1 \<and> m2 - rat_of_int \<lfloor>m2\<rfloor> = x1" using tassms
          by (simp add: x1_bt_01) 
        then obtain m2::rat where m2_prop: "m2 > 1 \<and> m2 - rat_of_int \<lfloor>m2\<rfloor>  = x1" by auto
      define m2m2::rat where m2m2_prop: "m2m2 = m2 -  rat_of_int \<lfloor>m2\<rfloor>"
      have "m2 > 1"
        using m2_prop by simp
      then have "\<lfloor>m2\<rfloor> > 0" by simp
      then have "(f (rat_of_int \<lfloor>m2\<rfloor>)) = real_of_int \<lfloor>m2\<rfloor>" using sploinky3
        by (smt (z3) f1case of_int_1 of_int_1_less_iff of_rat_of_int_eq one_le_floor order_less_imp_le) 
      have "(f m2) \<ge> (f (rat_of_int \<lfloor>m2\<rfloor>)) + (f (m2 - rat_of_int \<lfloor>m2\<rfloor>)) " using assms(2)
        by (metis \<open>0 < \<lfloor>m2\<rfloor>\<close> add.commute diff_add_cancel m2_prop of_int_pos x1_bt_01)
      then have "(real_of_rat m2) \<ge> (real_of_int \<lfloor>m2\<rfloor>) + (f (m2m2))"
        by (simp add: \<open>f (rat_of_int \<lfloor>m2\<rfloor>) = real_of_int \<lfloor>m2\<rfloor>\<close> m2_prop sploinky3 m2m2_prop)
      then have "real_of_rat m2m2 \<ge> (f m2m2)"
        by (simp add: of_rat_diff m2m2_prop)
      thus ?thesis
        by (simp add: m2_prop m2m2_prop)  qed qed
  fix x::"rat"
  assume x_gt_0:"x>0"
  assume x_lt_1: "x<1"
  then show "f x \<le> real_of_rat x" using caseInterval2Helper[of x] x_gt_0 x_lt_1 by auto  qed

(*proof of f_is_identity *)
  fix x::"rat"
  assume x_gt_0: "x>0"
  then show " f x = real_of_rat x" using caseInterval sploinky3 
  proof -
    have "x \<ge> 1 \<or> x < 1" by auto
    have h1:"(x \<ge> 1) \<Longrightarrow>  f x = real_of_rat x" using sploinky3[of x] f1case by fastforce
    have h2:"(x<1) \<Longrightarrow> (f x) = real_of_rat x" using caseInterval[of x] x_gt_0  caseInterval2[of x] by auto
    show ?thesis using h1 h2 by force qed qed
