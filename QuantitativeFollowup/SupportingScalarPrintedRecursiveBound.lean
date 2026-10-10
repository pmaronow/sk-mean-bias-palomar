module
public import QuantitativeFollowup.ScalarJetDynkin
public import FourPapersCommon.ExponentialVolterraRemainder

@[expose] public section

/-! Exact recursive exponential sup bound for the actual positive scalar
jets, obtained from the genuine restart Dynkin law and factorial iteration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper MvPolynomial
open scoped NNReal Topology BigOperators BoundedContinuousFunction
namespace QuantitativeFollowup
open FRSB FourPapersCommon
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

def scalarPrintedPositiveJetNorm (β : ℝ) (μ : Paper.ParisiMeasure) (r : ℕ) : ℝ :=
  ‖bcfSpatialDerivative (parisiGradientBCF β μ) r‖

def scalarPrintedJetSlice (β : ℝ) (μ : Paper.ParisiMeasure) (r : ℕ) (q : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>parisiSpatialJet β μ (r+1) q x)
    ((continuous_parisiSpatialJet_succ β μ r).comp (continuous_const.prodMk continuous_id))
    (scalarPrintedPositiveJetNorm β μ r)
    (fun x=>norm_parisiSpatialJet_succ_le β μ r q x)

def scalarPrintedJetRemainderNorm (β : ℝ) (μ : Paper.ParisiMeasure) (j : ℕ) : ℝ :=
  β^2/2*∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
    scalarPrintedPositiveJetNorm β μ i*scalarPrintedPositiveJetNorm β μ (j-i)

private theorem nonlinearJetField_printed (β : ℝ) (μ : Paper.ParisiMeasure)
    (j : ℕ) (hj : 3≤j) (q x : ℝ) :
    polynomialJetField β μ (nonlinearJetPolynomial (j-1)) q x=
      2*(j : ℝ)*parisiSpatialJet β μ 2 q x*parisiSpatialJet β μ j q x+
        ∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*parisiSpatialJet β μ (i+1) q x*
          parisiSpatialJet β μ (j-i+1) q x := by
  let F:=fun i=>(j.choose i : ℝ)*parisiSpatialJet β μ (i+1) q x*
    parisiSpatialJet β μ (j-i+1) q x
  have he : polynomialJetField β μ (nonlinearJetPolynomial (j-1)) q x=
      ∑i∈Finset.Icc 1 (j-1),F i := by
    simp only [polynomialJetField,nonlinearJetPolynomial,map_sum,map_mul,eval_C,eval_X,
      show j-1+1=j by omega,F]
  have hs : (∑i∈Finset.Icc 1 (j-1),F i)=
      F 1+(∑i∈Finset.Icc 2 (j-2),F i)+F (j-1) := by
    have hh := Finset.sum_Icc_succ_top (by omega : 1≤(j-2)+1) F
    rw [show j-2+1=j-1 by omega] at hh
    rw [hh]
    have hset : Finset.Icc 1 (j-2)=insert 1 (Finset.Icc 2 (j-2)) := by
      ext i
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    rw [hset,Finset.sum_insert (by simp)]
  have hchoose : j.choose (j-1)=j := by
    rw [Nat.choose_symm (by omega : 1≤j),Nat.choose_one_right]
  rw [he,hs]
  simp only [F,Nat.choose_one_right,hchoose,show j-1+1=j by omega,
    show j-(j-1)+1=2 by omega,show j-1+1=j by omega]
  norm_num only
  ring

private theorem scalarPrintedJetRemainderNorm_nonneg (β : ℝ)
    (μ : Paper.ParisiMeasure) (j : ℕ) : 0 ≤ scalarPrintedJetRemainderNorm β μ j := by
  unfold scalarPrintedJetRemainderNorm scalarPrintedPositiveJetNorm
  positivity

private theorem nonlinearJetField_printed_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (j : ℕ) (hj : 3≤j) (q x G : ℝ) (hG : 0≤G)
    (hjet : ‖parisiSpatialJet β μ j q x‖≤G) :
    ‖-(β^2*parisiCDF μ q/2)*
      polynomialJetField β μ (nonlinearJetPolynomial (j-1)) q x‖≤
        (j : ℝ)*β^2*G+scalarPrintedJetRemainderNorm β μ j := by
  have hcoef : β^2*parisiCDF μ q/2≤β^2/2 := by
    nlinarith [mul_le_mul_of_nonneg_left (parisiCDF_le_one μ q) (sq_nonneg β)]
  have hh : ‖parisiSpatialJet β μ 2 q x‖≤1 := by
    rw [parisiSpatialJet_two]
    exact norm_parisiHessian_le_one_all β μ (q,x)
  have hs : ‖∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
      parisiSpatialJet β μ (i+1) q x*parisiSpatialJet β μ (j-i+1) q x‖≤
      ∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
        scalarPrintedPositiveJetNorm β μ i*scalarPrintedPositiveJetNorm β μ (j-i) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_parisiSpatialJet_succ_le β μ i q x) (Nat.cast_nonneg _))
      (norm_parisiSpatialJet_succ_le β μ (j-i) q x) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hCDF := parisiCDF_nonneg μ q
  rw [norm_mul,norm_neg,Real.norm_of_nonneg
    (by positivity : 0≤β^2*parisiCDF μ q/2)]
  apply (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans
  rw [nonlinearJetField_printed β μ j hj]
  have ht : ‖2*(j : ℝ)*parisiSpatialJet β μ 2 q x*parisiSpatialJet β μ j q x‖≤2*j*G := by
    simp only [norm_mul,Real.norm_of_nonneg (by positivity : 0≤(2 : ℝ)),
      Real.norm_of_nonneg (Nat.cast_nonneg j)]
    have hprod := mul_le_mul hh hjet (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)
    nlinarith
  have hb := (norm_add_le _ _).trans (add_le_add ht hs)
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0≤β^2/2)
  dsimp only [scalarPrintedJetRemainderNorm]
  nlinarith [hm]

private theorem scalarPrintedJet_restart_comparison (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (j : ℕ) (hj : 3≤j)
    (g : ℝ→ℝ) (hg : Continuous g)
    (hg0 : ∀t∈Icc (0 : ℝ) 1,0≤g t)
    (hG : ∀q∈Icc (0 : ℝ) 1,∀x,
      ‖parisiSpatialJet β μ j q x‖≤g (1-q))
    (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    ‖parisiSpatialJet β μ j a x‖≤
      (‖scalarPrintedJetSlice β μ (j-1) 1‖+scalarPrintedJetRemainderNorm β μ j)+
        (j : ℝ)*β^2*(∫r in (0 : ℝ)..(1-a),g r) := by
  let X:=canonicalParisiRestartState β x μ a ha.1
  let d:=canonicalParisiRestartDrift β x μ a ha.1
  let hc:=boundedDriftItoCharacteristics_canonicalParisiRestartState β x μ a ha.1
  let T:=1-a
  let K:=(j : ℝ)*β^2
  let S:=scalarPrintedJetRemainderNorm β μ j
  let E:=fun r : ℝ=>K*g (T-r)+S
  have hT : 0≤T := by dsimp only [T];linarith [ha.2]
  have hT1 : T≤1 := by dsimp only [T];linarith [ha.1]
  have hS : 0≤S:=scalarPrintedJetRemainderNorm_nonneg β μ j
  have hEi : IntervalIntegrable E volume 0 T :=
    (by fun_prop : Continuous E).intervalIntegrable 0 T
  have hs (r : ℝ) (hr : r∈Ioc (0 : ℝ) T) :
      ‖∫ω,scalarDynkinSource X d β β μ (MvPolynomial.X (j-1)) a r ω
        ∂canonicalBrownianMeasure‖≤E r := by
    have hat : a+r∈Icc (0 : ℝ) 1:=⟨by linarith [ha.1,hr.1],by
      dsimp only [T] at hr;linarith [hr.2]⟩
    have ht : T-r∈Icc (0 : ℝ) 1:=⟨by linarith [hr.2],by linarith [hr.1]⟩
    have hpoint (ω : Paper.BrownianSample) :
        ‖scalarDynkinSource X d β β μ (MvPolynomial.X (j-1)) a r ω‖≤E r := by
      let y:=X r.toNNReal ω
      have hdr : d r.toNNReal ω=β^2*parisiCDF μ (a+r)*
          parisiSpatialJet β μ 1 (a+r) y := by
        simpa only [d,X,Real.coe_toNNReal _ hr.1.le,parisiSpatialJet_one] using
          canonicalParisiRestartDrift_eq β x μ a ha.1 r.toNNReal
            (by rw [Real.coe_toNNReal _ hr.1.le];linarith [hr.2,ha.1]) ω
      rw [scalarDynkinSource_spatialJet,hdr]
      simp only [y,sub_self,zero_div,zero_mul,add_zero]
      have hh := nonlinearJetField_printed_bound β μ j hj (a+r) y (g (T-r))
        (hg0 _ ht) (by simpa only [T,show 1-(a+r)=1-a-r by ring] using hG (a+r) hat y)
      exact hh
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure) (.of_forall hpoint)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall hs) hEi
  have htail:=scalarDynkin_tail hc β hβ μ (MvPolynomial.X (j-1)) a ha
  have hstart : scalarDynkinMoment canonicalBrownianMeasure X β μ (MvPolynomial.X (j-1)) a 0=
      parisiSpatialJet β μ j a x := by
    simp only [scalarDynkinMoment,scalarDynkinField_spatialJet,show j-1+1=j by omega,
      Real.toNNReal_zero,add_zero,X,canonicalParisiRestartState_zero]
    simp
  have hterm : ‖scalarDynkinMoment canonicalBrownianMeasure X β μ (MvPolynomial.X (j-1)) a T‖≤
      ‖scalarPrintedJetSlice β μ (j-1) 1‖ := by
    unfold scalarDynkinMoment
    have hb := norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure)
      (.of_forall fun ω=>(scalarPrintedJetSlice β μ (j-1) 1).norm_coe_le_norm (X T.toNNReal ω))
    simp only [probReal_univ,mul_one] at hb
    change ‖∫ω,parisiSpatialJet β μ (j-1+1) 1 (X T.toNNReal ω)
      ∂canonicalBrownianMeasure‖≤‖scalarPrintedJetSlice β μ (j-1) 1‖ at hb
    simpa only [scalarDynkinField_spatialJet,show j-1+1=j by omega,
      T,add_sub_cancel,probReal_univ,mul_one] using hb
  rw [hstart] at htail
  have heq : parisiSpatialJet β μ j a x=
      scalarDynkinMoment canonicalBrownianMeasure X β μ (MvPolynomial.X (j-1)) a T-
        ∫r in (0 : ℝ)..T,∫ω,scalarDynkinSource X d β β μ (MvPolynomial.X (j-1)) a r ω
          ∂canonicalBrownianMeasure := by
    change _=∫r in (0 : ℝ)..T,∫ω,
      scalarDynkinSource X d β β μ (MvPolynomial.X (j-1)) a r ω ∂canonicalBrownianMeasure at htail
    linarith
  rw [heq]
  apply ((norm_sub_le _ _).trans (add_le_add hterm hbound)).trans
  have he : (∫r in (0 : ℝ)..T,E r)=K*(∫r in (0 : ℝ)..T,g r)+S*T := by
    rw [intervalIntegral.integral_add
      (((by fun_prop : Continuous (fun r : ℝ=>g (T-r))).intervalIntegrable 0 T).const_mul K)
      intervalIntegrable_const,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left g T]
    simp only [sub_self,sub_zero,intervalIntegral.integral_const,smul_eq_mul]
    ring
  rw [he]
  dsimp only [K,S,T]
  nlinarith [mul_le_mul_of_nonneg_left hT1 hS]

theorem scalarPrintedHigherJet_pointwise_recursive_bound (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (j : ℕ) (hj : 3≤j) (q x : ℝ)
    (hq : q∈Icc (0 : ℝ) 1) :
    ‖parisiSpatialJet β μ j q x‖≤Real.exp ((j : ℝ)*β^2)*
      (‖scalarPrintedJetSlice β μ (j-1) 1‖+scalarPrintedJetRemainderNorm β μ j) := by
  let A:=‖scalarPrintedJetSlice β μ (j-1) 1‖+scalarPrintedJetRemainderNorm β μ j
  let B:=scalarPrintedPositiveJetNorm β μ (j-1)
  let K:=(j : ℝ)*β^2
  have hA : 0≤A:=add_nonneg (norm_nonneg _) (scalarPrintedJetRemainderNorm_nonneg β μ j)
  have hB : 0≤B:=norm_nonneg _
  have hK : 0≤K:=by positivity
  have H (n : ℕ) : ∀a∈Icc (0 : ℝ) 1,∀y : ℝ,
      ‖parisiSpatialJet β μ j a y‖≤A*Real.exp (K*(1-a))+B*(K*(1-a))^n/(n.factorial : ℝ) := by
    induction n with
    | zero =>
      intro a ha y
      have hh:=norm_parisiSpatialJet_succ_le β μ (j-1) a y
      rw [show j-1+1=j by omega] at hh
      simpa only [B,scalarPrintedPositiveJetNorm,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] using
        hh.trans (le_add_of_nonneg_left (mul_nonneg hA (Real.exp_pos _).le))
    | succ n hn =>
      intro a ha y
      let g:=fun r : ℝ=>A*Real.exp (K*r)+B*(K*r)^n/(n.factorial : ℝ)
      have hg : Continuous g:=by fun_prop
      have hg0 : ∀r∈Icc (0 : ℝ) 1,0≤g r:=by
        intro r hr
        have hKr:=mul_nonneg hK hr.1
        dsimp only [g]
        positivity
      have hh:=scalarPrintedJet_restart_comparison β hβ μ j hj g hg hg0 hn a y ha
      change ‖parisiSpatialJet β μ j a y‖≤A+K*(∫r in (0 : ℝ)..(1-a),g r) at hh
      exact hh.trans_eq (exponentialVolterraRemainder_integral A B K (1-a) n)
  have hlim : Tendsto (fun n : ℕ=>A*Real.exp (K*(1-q))+B*(K*(1-q))^n/(n.factorial : ℝ))
      atTop (𝓝 (A*Real.exp (K*(1-q)))) := by
    have hh:=(FloorSemiring.tendsto_pow_div_factorial_atTop (K*(1-q))).const_mul B
    simpa only [mul_div_assoc,mul_zero,add_zero] using tendsto_const_nhds.add hh
  have hp:=ge_of_tendsto hlim (.of_forall fun n=>H n q hq x)
  have he:Real.exp (K*(1-q))≤Real.exp K:=Real.exp_le_exp.mpr (by nlinarith [hq.1])
  exact hp.trans (by
    dsimp only [A,K]
    nlinarith [mul_le_mul_of_nonneg_left he hA])

theorem scalarPrintedHigherJet_recursive_sup_bound (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (j : ℕ) (hj : 3≤j) :
    scalarPrintedPositiveJetNorm β μ (j-1)≤Real.exp ((j : ℝ)*β^2)*
      (‖scalarPrintedJetSlice β μ (j-1) 1‖+β^2/2*
        ∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
          scalarPrintedPositiveJetNorm β μ i*scalarPrintedPositiveJetNorm β μ (j-i)) := by
  apply (BoundedContinuousFunction.norm_le (by
    unfold scalarPrintedPositiveJetNorm
    positivity)).mpr
  intro p
  have hp:=scalarPrintedHigherJet_pointwise_recursive_bound β hβ μ j hj p.1 p.2 p.1.property
  have he : parisiSpatialJet β μ j (p.1:ℝ) p.2=
      bcfSpatialDerivative (parisiGradientBCF β μ) (j-1) p := by
    simp only [parisiSpatialJet,show j≠0 by omega,ite_false,parisiSlabExtend]
    rw [projIcc_of_mem _ p.1.property]
  rw [he] at hp
  exact hp

theorem scalarPrintedJetSlice_terminal_log_two_cosh (β : ℝ)
    (μ : Paper.ParisiMeasure) (r : ℕ) (x : ℝ) :
    scalarPrintedJetSlice β μ r 1 x=
      iteratedDeriv (r+1) (fun y : ℝ=>Real.log (2*Real.cosh y)) x := by
  have hderiv : deriv (fun y : ℝ=>Real.log (2*Real.cosh y))=Real.tanh := by
    funext y
    have hh:=((Real.hasDerivAt_cosh y).const_mul 2).log
      (by positivity : 2*Real.cosh y≠0)
    convert hh.deriv using 1
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  change parisiSpatialJet β μ (r+1) 1 x=_
  rw [parisiSpatialJet_succ_eq_gradient_derivative,iteratedDeriv_succ',hderiv]
  congr 2
  exact funext (parisiGradient_terminal β μ)

theorem scalarPrintedHigherJet_recursive_variance_window (β d : ℝ)
    (hβ : 0<β) (hd : d∈Icc (β^2/2) (β^2)) (μ : Paper.ParisiMeasure)
    (j : ℕ) (hj : 3≤j) :
    scalarPrintedPositiveJetNorm (Real.sqrt d) μ (j-1)≤Real.exp ((j : ℝ)*β^2)*
      (‖scalarPrintedJetSlice (Real.sqrt d) μ (j-1) 1‖+β^2/2*
        ∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
          scalarPrintedPositiveJetNorm (Real.sqrt d) μ i*
          scalarPrintedPositiveJetNorm (Real.sqrt d) μ (j-i)) := by
  have hdpos : 0<d:=lt_of_lt_of_le (by positivity : 0<β^2/2) hd.1
  have hroot : Real.sqrt d≠0:=(Real.sqrt_pos.mpr hdpos).ne'
  have hsq : (Real.sqrt d)^2=d:=Real.sq_sqrt hdpos.le
  have hp:=scalarPrintedHigherJet_recursive_sup_bound (Real.sqrt d) hroot μ j hj
  have hsum : 0≤∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
      scalarPrintedPositiveJetNorm (Real.sqrt d) μ i*
      scalarPrintedPositiveJetNorm (Real.sqrt d) μ (j-i) := by
    unfold scalarPrintedPositiveJetNorm
    positivity
  have ha : 0≤‖scalarPrintedJetSlice (Real.sqrt d) μ (j-1) 1‖+d/2*
      ∑i∈Finset.Icc 2 (j-2),(j.choose i : ℝ)*
        scalarPrintedPositiveJetNorm (Real.sqrt d) μ i*
        scalarPrintedPositiveJetNorm (Real.sqrt d) μ (j-i) :=
    add_nonneg (norm_nonneg _) (mul_nonneg (by positivity) hsum)
  rw [hsq] at hp
  apply hp.trans
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd.2 (Nat.cast_nonneg j))
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith [hd.2] : d/2≤β^2/2) hsum)
  · exact ha
  · exact (Real.exp_pos _).le

end QuantitativeFollowup
