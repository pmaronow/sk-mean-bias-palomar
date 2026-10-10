module
public import QuantitativeFollowup.OneSignCoercivityTests
public import QuantitativeFollowup.VectorActualLipschitzResponse
public import QuantitativeFollowup.FollowupVariationalSourceFacts
public import FourPapersCommon.ResponseCoercivity

@[expose] public section

/-! Literal follow-up Lemma5.3 for the actual finite-dimensional functional.
The cutoff hypotheses and Stieltjes density are precisely the geometric
inputs of the paper. The response, curvature sign, and response upper bound
are proved facts of the constructed model, not supplied hypotheses. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory Paper QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def oneSignEnergyStieltjes (μ : Paper.ParisiMeasure) (β : ℝ) : Measure ℝ :=
  (ENNReal.ofReal β • (μ : Measure Paper.Overlap)).map (fun q : Paper.Overlap=>(q:ℝ))

/-- This is the real value of the paper's minimum with Δ/0=+infinity.
At Δ=0 it is zero, including at zero density. -/
def oneSignCoercivityMinimum (Δ B d : ℝ) : ℝ :=
  if d=0 then Δ^2/B else min (Δ^2/B) (Δ/d)

@[simp] theorem oneSignCoercivityMinimum_zero (B d : ℝ) :
    oneSignCoercivityMinimum 0 B d=0 := by
  unfold oneSignCoercivityMinimum
  split_ifs <;> simp

theorem oneSignCoercivityMinimum_monotone (B d : ℝ) (hB : 0<B) (hd : 0≤d) :
    MonotoneOn (fun Δ=>oneSignCoercivityMinimum Δ B d) (Ici (0:ℝ)) := by
  intro x hx y hy hxy
  unfold oneSignCoercivityMinimum
  by_cases hdz : d=0
  · simp only [hdz,if_pos]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 2) hB.le
  · simp only [hdz,if_neg]
    exact coercivity_min_monotone B d hB (lt_of_le_of_ne hd (Ne.symm hdz)) hx hxy

theorem followup_one_sign_coercivity (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho θ : ℝ) (hβ : 0<β) (hlam : 0≤lam) (hrho : 0<rho)
    (hθ : θ∈Ioo (0:ℝ) 1) (I : Set ℝ) (hI : closure I⊆Ioo (0:ℝ) 1)
    (φ : ℝ→ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hφ01 : ∀q∈Icc (0:ℝ) 1,φ q∈Icc (0:ℝ) 1)
    (hoff : ∀q∉I,φ q=0) (hne : ∃q∈Icc (0:ℝ) 1,φ q≠0)
    (A d σ : ℝ) (hA : 0<A) (hd : 0≤d) (hσ : |σ|=1)
    (hsign : ∀q∈I,A/2≤σ*(responseProfile ν β q-responseProfile μ β q))
    (hdensity : (oneSignEnergyStieltjes (parisiMix μ ν θ) β).restrict I≤ENNReal.ofReal d • volume) :
    let ht : 1-rho≤1 := by linarith
    let f := fun y=>followupEnergyFunctional n β lam rho (parisiMix μ ν y)
    let ζ := responseAveragedCurvatureReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht
    let Δ := rho*(∫q in (0:ℝ)..1,ζ q*φ q)
    let Y0 := ∫q in (0:ℝ)..1,(deriv φ q)^2
    0<Y0 ∧ rho*A^2/72*oneSignCoercivityMinimum Δ (β*Y0) d ≤ iteratedDeriv 2 f θ := by
  dsimp only
  have ht : 1-rho<1 := by linarith
  let ρμ:=parisiMix μ ν θ
  let ζ:=responseAveragedCurvatureReal (n:=n) ρμ β (1-rho) lam ht.le
  let b:=responseMeanHessianReal (n:=n) ρμ β (1-rho) lam ht.le
  let ψ:=fun q=>responseProfile ν β q-responseProfile μ β q
  let F:=iteratedDeriv 2 (fun y=>followupEnergyFunctional n β lam rho (parisiMix μ ν y)) θ
  let Δ:=rho*(∫q in (0:ℝ)..1,ζ q*φ q)
  let Y0:=∫q in (0:ℝ)..1,(deriv φ q)^2
  let Y:=∫q in (0:ℝ)..1,b q*(deriv φ q)^2
  let Z:=rho*(∫q : Paper.Overlap,(φ q)^2*responseAveragedCurvature (n:=n) ρμ β (1-rho) lam ht.le q
    ∂(ENNReal.ofReal β • (ρμ : Measure Paper.Overlap)))
  have hIo : I⊆Ioo (0:ℝ) 1:=subset_closure.trans hI
  have hsupp : tsupport φ⊆Ioo (0:ℝ) 1 :=
    (closure_mono (show Function.support φ⊆I from fun q hq=>by
      by_contra h;exact hq (hoff q h))).trans hI
  have h0 : φ 0=0:=hoff 0 (fun h=>lt_irrefl (0:ℝ) (hIo h).1)
  have h1 : φ 1=0:=hoff 1 (fun h=>lt_irrefl (1:ℝ) (hIo h).2)
  let w : ResponseLipschitzTest:=⟨φ,K,hφ,h0,h1⟩
  have hY0 : 0<Y0:=oneSignCutoff_energy_pos w hne
  have hp01 : ∀q,φ q∈Icc (0:ℝ) 1 := by
    intro q
    by_cases hq : q∈Icc (0:ℝ) 1
    · exact hφ01 q hq
    · rw [hoff q (fun hi=>hq ⟨(hIo hi).1.le,(hIo hi).2.le⟩)]
      exact ⟨le_rfl,zero_le_one⟩
  have hzcont : Continuous ζ:=continuous_responseAveragedCurvatureReal ρμ β (1-rho) lam ht
  have hbcont : Continuous b:=continuous_responseMeanHessianReal ρμ β (1-rho) lam ht.le
  have hz0 : ∀q,0≤ζ q:=fun q=>responseAveragedCurvature_nonneg ρμ β (1-rho) lam ht.le _
  have hb0 : ∀q,0≤b q:=fun q=>responseMeanHessian_nonneg ρμ β (1-rho) lam hβ.le ht.le _
  have hbβ : ∀q,b q≤β:=fun q=>responseMeanHessian_le_beta hn ρμ β (1-rho) lam hβ ht _
  have hF : 0≤F:=responseEnergyFunctional_mix_curvature_nonneg hn μ ν β (1-rho) lam θ hβ ht hlam hθ
  have hΔ : 0≤Δ:=mul_nonneg hrho.le
    (intervalIntegral.integral_nonneg zero_le_one (fun q _=>mul_nonneg (hz0 q) (hp01 q).1))
  have hY : 0≤Y:=intervalIntegral.integral_nonneg zero_le_one (fun q _=>mul_nonneg (hb0 q) (sq_nonneg _))
  have hYB : Y≤β*Y0 := by
    have hi:=oneSignCutoff_energy_integrable w
    have hh:=intervalIntegral.integral_mono_on zero_le_one
      (hi.continuousOn_mul hbcont.continuousOn) (hi.const_mul β)
      (fun q _=>mul_le_mul_of_nonneg_right (hbβ q) (sq_nonneg (deriv φ q)))
    simpa only [intervalIntegral.integral_const_mul,ResponseLipschitzTest.slope,w] using hh
  have hZmap : (∫q : Paper.Overlap,(φ q)^2*responseAveragedCurvature (n:=n) ρμ β (1-rho) lam ht.le q
      ∂(ENNReal.ofReal β • (ρμ : Measure Paper.Overlap)))=
      ∫q : ℝ,(φ q)^2*ζ q∂oneSignEnergyStieltjes ρμ β := by
    rw [oneSignEnergyStieltjes]
    have hm:=integral_map (μ:=ENNReal.ofReal β • (ρμ : Measure Paper.Overlap))
      (φ:=fun q : Paper.Overlap=>(q:ℝ)) (f:=fun q : ℝ=>(φ q)^2*ζ q)
      continuous_subtype_val.measurable.aemeasurable
      (((hφ.continuous.pow 2).mul hzcont).measurable.aestronglyMeasurable)
    rw [hm]
    apply integral_congr_ae
    filter_upwards with q
    simp only [ζ,responseAveragedCurvatureReal,projIcc_val]
  have hZ : 0≤Z := by
    unfold Z
    rw [hZmap]
    exact mul_nonneg hrho.le (integral_nonneg (fun q=>mul_nonneg (sq_nonneg _) (hz0 q)))
  have hZd : Z≤d*Δ := by
    have hh:=mul_le_mul_of_nonneg_left (oneSignCutoff_density_bound I hIo φ ζ hφ.continuous hzcont
      hp01 hz0 hoff (oneSignEnergyStieltjes ρμ β) d hd hdensity) hrho.le
    unfold Z
    rw [hZmap]
    convert hh using 1 <;> dsimp only [Δ] <;> ring
  have hψ : IntervalIntegrable ψ volume 0 1 :=
    ((parisiCDF_intervalIntegrable ν 0 1).const_mul β).sub ((parisiCDF_intervalIntegrable μ 0 1).const_mul β)
  have hpair:=oneSignCutoff_signed_pairing I φ ζ ψ hφ.continuous hzcont hψ
    (fun q=>(hp01 q).1) hz0 hoff A σ hσ hsign
  have hresp:=localization_compact_Lipschitz_response hn μ ν β lam rho θ hβ hlam hrho hθ φ K hφ hsupp
  dsimp only at hresp
  have hresponse : A*Δ/2≤Real.sqrt (F/rho)*(Real.sqrt Y+2*Real.sqrt (Y+Z)) := by
    calc
      A*Δ/2=rho*((A/2)*(∫q in (0:ℝ)..1,ζ q*φ q)):=by dsimp only [Δ];ring
      _≤rho*|∫q in (0:ℝ)..1,ψ q*ζ q*φ q|:=mul_le_mul_of_nonneg_left hpair hrho.le
      _≤_:=hresp
  refine ⟨hY0,?_⟩
  change rho*A^2/72*oneSignCoercivityMinimum Δ (β*Y0) d≤F
  unfold oneSignCoercivityMinimum
  by_cases hdz : d=0
  · simp only [hdz,if_pos]
    have hc:=response_coercivity_zero_density F rho A Δ Y Z (β*Y0) hF hrho hA.le hΔ hY hZ
      (mul_pos hβ hY0) hYB (by simpa only [hdz,zero_mul] using hZd) hresponse
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hβ hY0)).mpr
    have hc':=(div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<36) (mul_pos hβ hY0))).mp hc
    nlinarith
  · simp only [hdz,if_neg]
    exact response_coercivity F rho A Δ Y Z (β*Y0) d hF hrho hA.le hΔ hY hZ (mul_pos hβ hY0)
      (lt_of_le_of_ne hd (Ne.symm hdz)) hYB hZd hresponse

end QuantitativeFollowup
