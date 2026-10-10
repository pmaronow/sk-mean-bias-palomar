module
public import QuantitativeFollowup.OneSignCoercivitySource

@[expose] public section

/-! The revised one-sign coercivity lemma for every endpoint-zero Lipschitz
test.  The density hypothesis is the literal weighted Stieltjes inequality;
there is no compact-support or finite-interval hypothesis.  The model response,
its curvature sign and its Hessian upper bound are proved native facts. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory Paper QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal Topology ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem endpoint_zero_stieltjes_integral_interior
    (w : ResponseLipschitzTest) (ζ : Paper.Overlap → ℝ)
    (m : Measure Paper.Overlap) :
    (∫q : Paper.Overlap, (w.value q)^2 * ζ q ∂m) =
      ∫q in {q : Paper.Overlap | (q : ℝ) ∈ Ioo (0 : ℝ) 1},
        (w.value q)^2 * ζ q ∂m := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  have hz : w.value q = 0 := by
    by_cases h0 : (q : ℝ) = 0
    · simpa only [h0] using w.zero_left
    · have hp : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm h0)
      have h1 : (q : ℝ) = 1 := by
        by_contra h1
        exact hq ⟨hp, lt_of_le_of_ne q.property.2 h1⟩
      simpa only [h1] using w.zero_right
  simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul]

theorem one_sign_weighted_pairing (w : ResponseLipschitzTest)
    (ζ ψ : ℝ → ℝ) (hζ : Continuous ζ)
    (hψ : IntervalIntegrable ψ volume 0 1)
    (hw : ∀q ∈ Icc (0 : ℝ) 1, 0 ≤ w.value q)
    (hζ0 : ∀q, 0 ≤ ζ q) (A σ : ℝ) (hσ : |σ| = 1)
    (hsign : ∀q ∈ Icc (0 : ℝ) 1, 0 < w.value q → A/2 ≤ σ*ψ q) :
    A/2 * (∫q in (0 : ℝ)..1, ζ q * w.value q) ≤
      |∫q in (0 : ℝ)..1, ψ q * ζ q * w.value q| := by
  have hi : IntervalIntegrable (fun q => ψ q * ζ q * w.value q) volume 0 1 := by
    convert (hψ.continuousOn_mul hζ.continuousOn).continuousOn_mul w.continuous.continuousOn using 1
    funext q
    ring
  have hp : ∀q ∈ Icc (0 : ℝ) 1,
      (A/2)*(ζ q*w.value q) ≤ σ*(ψ q*ζ q*w.value q) := by
    intro q hq
    by_cases hpos : 0 < w.value q
    · have hh := mul_le_mul_of_nonneg_right (hsign q hq hpos)
        (mul_nonneg (hζ0 q) (hw q hq))
      convert hh using 1 <;> ring
    · have hz : w.value q = 0 := le_antisymm (le_of_not_gt hpos) (hw q hq)
      simp only [hz, mul_zero, le_refl]
  have hh := intervalIntegral.integral_mono_on zero_le_one
    (((hζ.mul w.continuous).intervalIntegrable (μ := volume) 0 1).const_mul (A/2))
    (hi.const_mul σ) hp
  simp only [intervalIntegral.integral_const_mul] at hh
  refine hh.trans ?_
  calc
    σ*(∫q in (0 : ℝ)..1, ψ q*ζ q*w.value q) ≤
        |σ*(∫q in (0 : ℝ)..1, ψ q*ζ q*w.value q)| := le_abs_self _
    _ = |∫q in (0 : ℝ)..1, ψ q*ζ q*w.value q| := by rw [abs_mul, hσ, one_mul]

/-- Literal Lemma 5.3 in the revised manuscript. The weighted-density
hypothesis is on the actual energy-coordinate Stieltjes measure β dμθ,
including all interior atoms. Endpoint atoms contribute zero. -/
theorem weighted_one_sign_coercivity (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β lam rho θ : ℝ) (hβ : 0 < β) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (hθ : θ ∈ Ioo (0 : ℝ) 1) (w : ResponseLipschitzTest)
    (hw : ∀q ∈ Icc (0 : ℝ) 1, w.value q ∈ Icc (0 : ℝ) 1)
    (hne : ∃q ∈ Icc (0 : ℝ) 1, w.value q ≠ 0)
    (A d σ : ℝ) (hA : 0 < A) (hd : 0 ≤ d) (hσ : |σ| = 1)
    (hsign : ∀q ∈ Icc (0 : ℝ) 1, 0 < w.value q →
      A/2 ≤ σ*(responseProfile ν β q - responseProfile μ β q)) :
    let ht : 1-rho ≤ 1 := by linarith
    let f := fun y => followupEnergyFunctional n β lam rho (parisiMix μ ν y)
    let ζ := responseAveragedCurvatureReal (n := n) (parisiMix μ ν θ) β (1-rho) lam ht
    let Δ := rho*(∫q in (0 : ℝ)..1, ζ q*w.value q)
    let Y0 := ∫q in (0 : ℝ)..1, (w.slope q)^2
    rho*(∫q in {q : Paper.Overlap | (q : ℝ) ∈ Ioo (0 : ℝ) 1},
      (w.value q)^2 * responseAveragedCurvature (n := n) (parisiMix μ ν θ)
        β (1-rho) lam ht q ∂(ENNReal.ofReal β • (parisiMix μ ν θ : Measure Paper.Overlap))) ≤ d*Δ →
    0 < Y0 ∧
      rho*A^2/72*oneSignCoercivityMinimum Δ (β*Y0) d ≤ iteratedDeriv 2 f θ ∧
      ∀δ, 0 ≤ δ → δ ≤ Δ →
        rho*A^2/72*oneSignCoercivityMinimum δ (β*Y0) d ≤ iteratedDeriv 2 f θ := by
  dsimp only
  intro hweighted
  have ht : 1-rho < 1 := by linarith
  let ρμ := parisiMix μ ν θ
  let ζ := responseAveragedCurvatureReal (n := n) ρμ β (1-rho) lam ht.le
  let b := responseMeanHessianReal (n := n) ρμ β (1-rho) lam ht.le
  let ψ := fun q => responseProfile ν β q - responseProfile μ β q
  let F := iteratedDeriv 2 (fun y => followupEnergyFunctional n β lam rho (parisiMix μ ν y)) θ
  let Δ := rho*(∫q in (0 : ℝ)..1, ζ q*w.value q)
  let Y0 := ∫q in (0 : ℝ)..1, (w.slope q)^2
  let Y := responseLipschitzMeanEnergy (n := n) μ ν β (1-rho) lam θ ht.le w
  let Z := responseLipschitzCurvatureEnergy (n := n) μ ν β (1-rho) lam θ ht.le w
  have hY0 : 0 < Y0 := oneSignCutoff_energy_pos w hne
  have hzcont : Continuous ζ := continuous_responseAveragedCurvatureReal ρμ β (1-rho) lam ht
  have hbcont : Continuous b := continuous_responseMeanHessianReal ρμ β (1-rho) lam ht.le
  have hz0 : ∀q, 0 ≤ ζ q := fun q => responseAveragedCurvature_nonneg ρμ β (1-rho) lam ht.le _
  have hbβ : ∀q, b q ≤ β := fun q => responseMeanHessian_le_beta hn ρμ β (1-rho) lam hβ ht _
  have hF : 0 ≤ F := responseEnergyFunctional_mix_curvature_nonneg hn μ ν β (1-rho) lam θ hβ ht hlam hθ
  have hΔ : 0 ≤ Δ := mul_nonneg hrho.le
    (intervalIntegral.integral_nonneg zero_le_one (fun q hq => mul_nonneg (hz0 q) (hw q hq).1))
  have hY : 0 ≤ Y := responseLipschitzMeanEnergy_nonneg μ ν β (1-rho) lam θ hβ.le ht.le w
  have hZ : 0 ≤ Z := responseLipschitzCurvatureEnergy_nonneg μ ν β (1-rho) lam θ hβ.le ht.le w
  have hYB : Y ≤ β*Y0 := by
    have hi := oneSignCutoff_energy_integrable w
    have hh := intervalIntegral.integral_mono_on zero_le_one
      (hi.continuousOn_mul hbcont.continuousOn) (hi.const_mul β)
      (fun q _ => mul_le_mul_of_nonneg_right (hbβ q) (sq_nonneg (w.slope q)))
    simpa only [Y, Y0, responseLipschitzMeanEnergy, b,
      intervalIntegral.integral_const_mul, mul_comm] using hh
  have hZeq : Z = rho*(∫q : Paper.Overlap, (w.value q)^2*
      responseAveragedCurvature (n := n) ρμ β (1-rho) lam ht.le q
      ∂(ENNReal.ofReal β • (ρμ : Measure Paper.Overlap))) := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hβ.le]
    simp only [Z, responseLipschitzCurvatureEnergy, smul_eq_mul, sub_sub_cancel]
    ring
  have hZd : Z ≤ d*Δ := by
    rw [hZeq, endpoint_zero_stieltjes_integral_interior]
    exact hweighted
  have hψ : IntervalIntegrable ψ volume 0 1 :=
    ((parisiCDF_intervalIntegrable ν 0 1).const_mul β).sub
      ((parisiCDF_intervalIntegrable μ 0 1).const_mul β)
  have hpair := one_sign_weighted_pairing w ζ ψ hzcont hψ
    (fun q hq => (hw q hq).1) hz0 A σ hσ hsign
  have hresp := localization_Lipschitz_response_test hn μ ν β lam rho θ hβ hlam hrho hθ w
  have hsig : responseLipschitzSignal (n := n) μ ν β (1-rho) lam θ ht.le w =
      ∫q in (0 : ℝ)..1, ψ q*ζ q*w.value q := by
    unfold responseLipschitzSignal
    apply intervalIntegral.integral_congr
    intro q _
    dsimp only [ψ, ζ, ρμ, responseProfile]
    ring
  rw [hsig] at hresp
  have hresponse : A*Δ/2 ≤ Real.sqrt (F/rho)*(Real.sqrt Y+2*Real.sqrt (Y+Z)) := by
    calc
      A*Δ/2 = rho*((A/2)*(∫q in (0 : ℝ)..1, ζ q*w.value q)) := by dsimp only [Δ]; ring
      _ ≤ rho*|∫q in (0 : ℝ)..1, ψ q*ζ q*w.value q| := mul_le_mul_of_nonneg_left hpair hrho.le
      _ ≤ _ := hresp
  have hbound : rho*A^2/72*oneSignCoercivityMinimum Δ (β*Y0) d ≤ F := by
    unfold oneSignCoercivityMinimum
    by_cases hdz : d = 0
    · simp only [hdz, if_pos]
      have hc := response_coercivity_zero_density F rho A Δ Y Z (β*Y0)
        hF hrho hA.le hΔ hY hZ (mul_pos hβ hY0) hYB
        (by simpa only [hdz, zero_mul] using hZd) hresponse
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (mul_pos hβ hY0)).mpr
      have hc' := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 36) (mul_pos hβ hY0))).mp hc
      nlinarith
    · simp only [hdz, if_neg]
      exact response_coercivity F rho A Δ Y Z (β*Y0) d hF hrho hA.le hΔ hY hZ
        (mul_pos hβ hY0) (lt_of_le_of_ne hd (Ne.symm hdz)) hYB hZd hresponse
  refine ⟨hY0, hbound, ?_⟩
  intro δ hδ hδΔ
  exact (mul_le_mul_of_nonneg_left
    (oneSignCoercivityMinimum_monotone _ d (mul_pos hβ hY0) hd hδ hΔ hδΔ)
    (by positivity : 0 ≤ rho*A^2/72)).trans hbound

/-- The manuscript's unit-interval formulation. The global test needed by
the native response theorem is constructed by clamping to `[0,1]`, so global
regularity is not an added hypothesis. -/
theorem weighted_one_sign_coercivity_unit_interval
    (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β lam rho θ : ℝ) (hβ : 0 < β) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (φ : Paper.Overlap → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hφ01 : ∀q, φ q ∈ Icc (0 : ℝ) 1)
    (hleft : φ ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = 0)
    (hright : φ ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 0)
    (hne : ∃q, φ q ≠ 0) (A d σ : ℝ)
    (hA : 0 < A) (hd : 0 ≤ d) (hσ : |σ| = 1)
    (hsign : ∀q : Paper.Overlap, 0 < φ q →
      A/2 ≤ σ*(responseProfile ν β q-responseProfile μ β q)) :
    let ht : 1-rho ≤ 1 := by linarith
    let f := fun y => followupEnergyFunctional n β lam rho (parisiMix μ ν y)
    let ζ := responseAveragedCurvatureReal (n := n) (parisiMix μ ν θ) β (1-rho) lam ht
    let Δ := rho*(∫q in (0 : ℝ)..1, ζ q*oneSignUnitTestExtension φ q)
    let Y0 := ∫q in (0 : ℝ)..1, (deriv (oneSignUnitTestExtension φ) q)^2
    rho*(∫q in {q : Paper.Overlap | (q : ℝ) ∈ Ioo (0 : ℝ) 1},
      (φ q)^2*responseAveragedCurvature (n := n) (parisiMix μ ν θ)
        β (1-rho) lam ht q ∂(ENNReal.ofReal β • (parisiMix μ ν θ : Measure Paper.Overlap))) ≤ d*Δ →
    0 < Y0 ∧
      rho*A^2/72*oneSignCoercivityMinimum Δ (β*Y0) d ≤ iteratedDeriv 2 f θ ∧
      ∀δ, 0 ≤ δ → δ ≤ Δ →
        rho*A^2/72*oneSignCoercivityMinimum δ (β*Y0) d ≤ iteratedDeriv 2 f θ := by
  dsimp only
  intro hweighted
  let w : ResponseLipschitzTest := {
    value := oneSignUnitTestExtension φ
    lipschitzBound := K
    lipschitz := oneSignUnitTestExtension_lipschitz φ K hφ
    zero_left := by
      simpa only [oneSignUnitTestExtension, projIcc_of_le_left zero_le_one le_rfl] using hleft
    zero_right := by
      simpa only [oneSignUnitTestExtension, projIcc_of_right_le zero_le_one le_rfl] using hright }
  have hw : ∀q ∈ Icc (0 : ℝ) 1, w.value q ∈ Icc (0 : ℝ) 1 :=
    fun q _ => hφ01 (projIcc 0 1 zero_le_one q)
  have hne' : ∃q ∈ Icc (0 : ℝ) 1, w.value q ≠ 0 := by
    obtain ⟨q, hq⟩ := hne
    refine ⟨q, q.property, ?_⟩
    simpa only [w, oneSignUnitTestExtension, projIcc_val] using hq
  have hs : ∀q ∈ Icc (0 : ℝ) 1, 0 < w.value q →
      A/2 ≤ σ*(responseProfile ν β q-responseProfile μ β q) := by
    intro q hq hpos
    have hp : 0 < φ ⟨q, hq⟩ := by
      simpa only [w, oneSignUnitTestExtension, projIcc_of_mem zero_le_one hq] using hpos
    exact hsign ⟨q, hq⟩ hp
  have hbase := weighted_one_sign_coercivity hn μ ν β lam rho θ hβ hlam hrho hθ
    w hw hne' A d σ hA hd hσ hs
  dsimp only at hbase
  have hc := hbase (by
    simpa only [w, oneSignUnitTestExtension, projIcc_val] using hweighted)
  simpa only [w, ResponseLipschitzTest.slope] using hc

/-- The sufficient condition stated immediately after the manuscript's
weighted-density inequality. The restriction is to the positive support,
which may approach either endpoint; no condition on its closure is used. -/
theorem weighted_density_of_positive_support_density
    (μ : Paper.ParisiMeasure) (β lam rho : ℝ) (hrho : 0 < rho)
    (φ : Paper.Overlap → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hφ01 : ∀q, φ q ∈ Icc (0 : ℝ) 1)
    (hleft : φ ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = 0)
    (hright : φ ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 0)
    (d : ℝ) (hd : 0 ≤ d)
    (hdensity : (oneSignEnergyStieltjes μ β).restrict
      {q : ℝ | 0 < oneSignUnitTestExtension φ q} ≤ ENNReal.ofReal d • volume) :
    let ht : 1-rho ≤ 1 := by linarith
    let ζ := responseAveragedCurvatureReal (n := n) μ β (1-rho) lam ht
    rho*(∫q in {q : Paper.Overlap | (q : ℝ) ∈ Ioo (0 : ℝ) 1},
      (φ q)^2*responseAveragedCurvature (n := n) μ β (1-rho) lam ht q
        ∂(ENNReal.ofReal β • (μ : Measure Paper.Overlap))) ≤
      d*(rho*(∫q in (0 : ℝ)..1, ζ q*oneSignUnitTestExtension φ q)) := by
  dsimp only
  have ht : 1-rho < 1 := by linarith
  let ζ := responseAveragedCurvatureReal (n := n) μ β (1-rho) lam ht.le
  let w : ResponseLipschitzTest := {
    value := oneSignUnitTestExtension φ
    lipschitzBound := K
    lipschitz := oneSignUnitTestExtension_lipschitz φ K hφ
    zero_left := by
      simpa only [oneSignUnitTestExtension, projIcc_of_le_left zero_le_one le_rfl] using hleft
    zero_right := by
      simpa only [oneSignUnitTestExtension, projIcc_of_right_le zero_le_one le_rfl] using hright }
  have h01 : ∀q, w.value q ∈ Icc (0 : ℝ) 1 :=
    fun q => hφ01 (projIcc 0 1 zero_le_one q)
  have hI : {q : ℝ | 0 < w.value q} ⊆ Ioo (0 : ℝ) 1 := by
    intro q hq
    have h0 : 0 < q := by
      by_contra h
      have hz : w.value q = 0 := by
        simpa only [w, oneSignUnitTestExtension,
          projIcc_of_le_left zero_le_one (le_of_not_gt h)] using hleft
      exact (ne_of_gt hq) hz
    have h1 : q < 1 := by
      by_contra h
      have hz : w.value q = 0 := by
        simpa only [w, oneSignUnitTestExtension,
          projIcc_of_right_le zero_le_one (le_of_not_gt h)] using hright
      exact (ne_of_gt hq) hz
    exact ⟨h0, h1⟩
  have hoff : ∀q ∉ {q : ℝ | 0 < w.value q}, w.value q = 0 := by
    intro q hq
    exact le_antisymm (le_of_not_gt hq) (h01 q).1
  have hzcont : Continuous ζ := continuous_responseAveragedCurvatureReal μ β (1-rho) lam ht
  have hz0 : ∀q, 0 ≤ ζ q :=
    fun q => responseAveragedCurvature_nonneg μ β (1-rho) lam ht.le _
  have hbound := oneSignCutoff_density_bound _ hI w.value ζ w.continuous hzcont
    h01 hz0 hoff (oneSignEnergyStieltjes μ β) d hd hdensity
  have hZmap :
      (∫q : Paper.Overlap, (φ q)^2*responseAveragedCurvature (n := n) μ β (1-rho) lam ht.le q
        ∂(ENNReal.ofReal β • (μ : Measure Paper.Overlap))) =
      ∫q : ℝ, (w.value q)^2*ζ q ∂oneSignEnergyStieltjes μ β := by
    rw [oneSignEnergyStieltjes]
    have hm := integral_map (μ := ENNReal.ofReal β • (μ : Measure Paper.Overlap))
      (φ := fun q : Paper.Overlap => (q : ℝ)) (f := fun q : ℝ => (w.value q)^2*ζ q)
      continuous_subtype_val.measurable.aemeasurable
      (((w.continuous.pow 2).mul hzcont).measurable.aestronglyMeasurable)
    rw [hm]
    apply integral_congr_ae
    filter_upwards with q
    simp only [w, ζ, oneSignUnitTestExtension, responseAveragedCurvatureReal, projIcc_val]
  have hfull :
      (∫q in {q : Paper.Overlap | (q : ℝ) ∈ Ioo (0 : ℝ) 1},
        (φ q)^2*responseAveragedCurvature (n := n) μ β (1-rho) lam ht.le q
        ∂(ENNReal.ofReal β • (μ : Measure Paper.Overlap))) =
      ∫q : Paper.Overlap, (φ q)^2*responseAveragedCurvature (n := n) μ β (1-rho) lam ht.le q
        ∂(ENNReal.ofReal β • (μ : Measure Paper.Overlap)) := by
    simpa only [w, oneSignUnitTestExtension, projIcc_val] using
      (endpoint_zero_stieltjes_integral_interior w
        (responseAveragedCurvature (n := n) μ β (1-rho) lam ht.le)
        (ENNReal.ofReal β • (μ : Measure Paper.Overlap))).symm
  rw [hfull, hZmap]
  have hh := mul_le_mul_of_nonneg_left hbound hrho.le
  convert hh using 1 <;> dsimp only [w, ζ] <;> ring

end HexagonPaper
