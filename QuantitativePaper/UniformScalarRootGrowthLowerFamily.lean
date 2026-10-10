module
public import QuantitativePaper.UniformScalarRootGrowthLowerMoment
public import QuantitativePaper.UniformScalarRootGrowthBoundaryData
public import QuantitativePaper.UniformScalarSmoothing
public import QuantitativePaper.ScalarEnergyCrudeUpper
public import QuantitativePaper.ScalarSupportEndpointLower
public import FRSB.FullSupport

@[expose] public section

/-! Uniform lower linear growth of the actual minimizing scalar profile.
All analytic and probabilistic inputs concern the actual PDE and diffusion. -/
noncomputable section
open Set MeasureTheory Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 2400000

private theorem scalar_lower_denominator_upper (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (q C : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (hcontact : FRSB.GammaPrime β μ q=1)
    (hH : ∀x,scalarEnergySpatialJet β μ 1 (q,x)≤C) :
    β^3*FRSB.quotientDenominator β μ q≤C := by
  have hp (ω : Paper.BrownianSample) :
      β^3*(FRSB.C β μ q ω)^3≤C*β^2*(FRSB.C β μ q ω)^2:=by
    have hh:=hH (FRSB.optimalStateReal β μ ω q/β)
    rw [scalarEnergySpatialJet_one,mul_div_cancel₀ _ hβ.ne',←FRSB.C_eq_hessian] at hh
    have hmul:=mul_le_mul_of_nonneg_right hh (sq_nonneg (β*FRSB.C β μ q ω))
    nlinarith
  have hi:=integral_mono
    ((FRSB.integrable_jetProcess_pow β hβ.ne' μ 1 3 hq).const_mul (β^3))
    ((FRSB.integrable_C_sq β hβ.ne' μ hq).const_mul (C*β^2)) hp
  rw [integral_const_mul,integral_const_mul] at hi
  have hd : (∫ω,FRSB.jetProcess β μ 2 q ω^3 ∂canonicalBrownianMeasure)=
      FRSB.quotientDenominator β μ q:=by
    simp only [FRSB.quotientDenominator,FRSB.quotientDenominatorPolynomial,FRSB.moment_X_pow,Nat.reduceAdd]
  rw [hd] at hi
  have he : β^2*(∫ω,FRSB.C β μ q ω^2 ∂canonicalBrownianMeasure)=1:=hcontact
  have hm:=congrArg (fun x:ℝ=>C*x) he
  nlinarith

/-- Literal lower-root family, uniform over all beta above the prescribed
beta0 and every actual zero-field minimizing Parisi measure. -/
theorem scalar_minimizer_uniform_root_lower (β₀ : ℝ) (hβ₀ : 1<β₀) :
    ∃k Tstar : ℝ,0<k ∧ Tstar∈Ioc (0:ℝ) (1/4) ∧
      ∀β,β₀≤β→∀μ,FRSB.IsParisiMinimizer β 0 μ→
        ∀q∈Icc (0:ℝ) Tstar,k*q≤β*parisiCDF μ q := by
  obtain ⟨C,hC,hjets⟩:=scalarEnergySpatialJet_uniform_early
  let CW:=C/2+32*(C+3*C^2)
  let delta:=1-1/β₀
  let τ:=min (1/8:ℝ) (min (delta/2) (3/(32*CW)))
  let K:=(1/4:ℝ)*uniformBoundaryAlpha τ*(3/32)*Real.exp (-uniformBoundaryAlpha τ)
  let Tstar:=min τ (min (1/4096:ℝ) (min (τ^2/256) (1/(256*C^2))))
  let k:=K^2*scalarBrownianWindowProbability/(32*C)
  have hCpos : 0<C:=zero_lt_one.trans_le hC
  have hCW : 0<CW:=by dsimp [CW];positivity
  have hdelta : 0<delta:=by
    dsimp only [delta]
    apply sub_pos.mpr
    exact (div_lt_iff₀ (zero_lt_one.trans hβ₀)).mpr (by simpa using hβ₀)
  have hτpos : 0<τ:=lt_min (by norm_num) (lt_min (half_pos hdelta) (by positivity))
  have hτquarter : τ≤1/4:=(min_le_left _ _).trans (by norm_num)
  have hτdelta : τ≤delta/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hτCW : CW*τ≤3/32:=by
    have hh : τ≤3/(32*CW):=(min_le_right _ _).trans (min_le_right _ _)
    have hm:=(le_div_iff₀ (mul_pos (by norm_num) hCW)).mp hh
    nlinarith
  have hK : 0<K:=by
    dsimp only [K]
    have ha : 0<uniformBoundaryAlpha τ:=by unfold uniformBoundaryAlpha;positivity
    positivity
  have hTs : Tstar∈Ioc (0:ℝ) (1/4):=⟨lt_min hτpos (lt_min (by norm_num)
    (lt_min (by positivity) (by positivity))),(min_le_left _ _).trans hτquarter⟩
  have hk : 0<k:=by dsimp [k];exact div_pos (mul_pos (sq_pos_of_pos hK)
    scalarBrownianWindowProbability_pos) (mul_pos (by norm_num) hCpos)
  refine ⟨k,Tstar,hk,hTs,?_⟩
  intro β hb μ hmin q hq
  have hβ1 : 1<β:=hβ₀.trans_le hb
  have hβ : 0<β:=zero_lt_one.trans hβ1
  obtain ⟨qend,hqend,hsupp⟩:=FRSB.minimizer_full_support β hβ1 μ hmin
  have hsupport : qend∈FRSB.parisiSupport μ:=by rw [hsupp];exact ⟨hqend.1.le,le_rfl⟩
  have htop:=scalar_support_max_ge_one_sub_inv β hβ μ hmin qend hsupport
    (fun x hx=>by rw [hsupp] at hx;exact hx.2)
  have hinv:=one_div_le_one_div_of_le (zero_lt_one.trans hβ₀) hb
  have hτend : τ<qend:=by dsimp only [delta] at hτdelta hdelta;linarith
  have hcost : scalarParisiFunctional β μ/β≤2:=
    (scalarEnergy_minimizer_cost_lt_three_halves β hβ1.le μ hmin).le.trans (by norm_num)
  have hjet (j : ℕ) (hj : j∈Finset.Icc 1 4) (r : ℝ) (hr : r∈Icc (0:ℝ) τ) (x : ℝ) :
      ‖scalarEnergySpatialJet β μ j (r,x)‖≤C:=hjets β hβ μ hcost j hj r ⟨hr.1,hr.2.trans hτquarter⟩ x
  have hcoeff (r : ℝ) (hr : r∈Icc (0:ℝ) τ) : β*parisiCDF μ r≤32:=
    scalarEnergy_sublevel_two_cdf_le β hβ μ hcost r (hr.2.trans (hτquarter.trans (by norm_num)))
  obtain ⟨ell,hell,helllo,hbar⟩:=exists_scalarEnergy_uniform_boundary_data β hβ μ hmin qend
    hqend hsupp C τ hC ⟨hτpos,hτquarter⟩ hτend hcoeff hjet hτCW
  have hqτ : q≤τ:=hq.2.trans (min_le_left _ _)
  have hqI : q∈Icc (0:ℝ) τ:=⟨hq.1,hqτ⟩
  by_cases hq0 : q=0
  · subst q
    simpa only [mul_zero] using mul_nonneg hβ.le (parisiCDF_nonneg μ 0)
  have hqp : 0<q:=lt_of_le_of_ne hq.1 (Ne.symm hq0)
  have hqsmall : q≤1/4096:=hq.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqτsq : q≤τ^2/256:=hq.2.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hqCsq : q≤1/(256*C^2):=hq.2.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hs : 0≤Real.sqrt q:=Real.sqrt_nonneg q
  have hsq : (Real.sqrt q)^2=q:=Real.sq_sqrt hqp.le
  have hsτ : Real.sqrt q≤τ/16:=by nlinarith
  have hsC : Real.sqrt q≤1/(16*C):=by
    have hm:=(le_div_iff₀ (by positivity : (0:ℝ)<256*C^2)).mp hqCsq
    apply (le_div_iff₀ (by positivity : (0:ℝ)<16*C)).mpr
    nlinarith [sq_nonneg (16*C*Real.sqrt q-1)]
  have hsell : 3*Real.sqrt q≤ell:=by
    have he : 3*(1/(16*C))=3/(16*C):=by ring
    exact (mul_le_mul_of_nonneg_left hsC (by norm_num)).trans (he.le.trans helllo)
  have hA:=scalarRootMomentA_brownian_lower β hβ μ τ ell K q hτpos hK.le
    ⟨hqp,hqsmall⟩ hqτ hsτ hsell (fun r hr=>hcoeff r ⟨hr.1,hr.2.trans hqτ⟩)
    (hbar q hqI)
  have hcontact:=FRSB.GammaPrime_eq_one_on_support_interval β hβ.ne' μ hmin qend hqend.1
    hqend.2.le hsupp q ⟨hq.1,hqτ.trans hτend.le⟩
  have hB:=scalar_lower_denominator_upper β hβ μ q C ⟨hq.1,hqτ.trans (hτquarter.trans (by norm_num))⟩
    hcontact (fun x=>(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hjet 1 (by decide) q hqI x))
  have hcdf:=FRSB.parisiCDF_eq_momentQuotient_on_support_interval β hβ.ne' μ hmin qend
    hqend.1 hqend.2.le hsupp q ⟨hq.1,hqτ.trans_lt hτend⟩
  have hden : 0<FRSB.quotientDenominator β μ q:=FRSB.quotientDenominator_pos β hβ.ne' μ
    q ⟨hq.1,hqτ.trans (hτquarter.trans (by norm_num))⟩
  have hident : β^4*FRSB.quotientNumerator β μ q=
      2*(β^3*FRSB.quotientDenominator β μ q)*(β*parisiCDF μ q):=by
    rw [hcdf,FRSB.momentQuotient]
    field_simp
    <;> ring
  rw [hident] at hA
  have hgn : 0≤β*parisiCDF μ q:=mul_nonneg hβ.le (parisiCDF_nonneg μ q)
  have hm:=mul_le_mul_of_nonneg_right hB hgn
  have hkdef : (K^2*scalarBrownianWindowProbability/16)*q=2*C*(k*q):=by
    dsimp only [k]
    field_simp
    <;> ring
  rw [hkdef] at hA
  nlinarith

end QuantitativePaper
