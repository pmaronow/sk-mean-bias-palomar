module
public import QuantitativePaper.ResponseLipschitzActualCurvature
public import QuantitativeFollowup.ReflectedFunctionalRegularization

@[expose] public section

/-! Literal arbitrary-profile response facts for the follow-up manuscript.
Closed C² regularity and the response inequality hold for every genuine
compactly supported Lipschitz test, with its a.e. derivative and all
Stieltjes atoms retained in the physical energy measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem localization_segment_contDiffOn_two (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho : ℝ) (hβ : β≠0) (hrho : 0<rho) :
    ContDiffOn ℝ 2
      (fun θ=>followupEnergyFunctional n β lam rho (parisiMix μ ν θ)) (Icc (0:ℝ) 1) := by
  exact contDiffOn_responseEnergyFunctional_mix_two hn μ ν β (1-rho) lam hβ (by linarith)

theorem localization_Lipschitz_response_test (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho θ : ℝ) (hβ : 0<β) (hlam : 0≤lam) (hrho : 0<rho)
    (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest) :
    rho*|responseLipschitzSignal (n:=n) μ ν β (1-rho) lam θ (by linarith) w|≤
      Real.sqrt (iteratedDeriv 2
        (fun y=>followupEnergyFunctional n β lam rho (parisiMix μ ν y)) θ/rho)*
      (Real.sqrt (responseLipschitzMeanEnergy (n:=n) μ ν β (1-rho) lam θ (by linarith) w)+
        2*Real.sqrt (responseLipschitzMeanEnergy (n:=n) μ ν β (1-rho) lam θ (by linarith) w+
          responseLipschitzCurvatureEnergy (n:=n) μ ν β (1-rho) lam θ (by linarith) w)) := by
  have hh:=response_Lipschitz_actual_squareRoot_bound hn μ ν β (1-rho) lam θ hβ
    (by linarith) hlam hθ w
  simpa only [sub_sub_cancel,responseEnergyFunctional,followupEnergyFunctional] using hh

theorem localization_compact_Lipschitz_response (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho θ : ℝ) (hβ : 0<β) (hlam : 0≤lam) (hrho : 0<rho)
    (hθ : θ∈Ioo (0:ℝ) 1) (φ : ℝ→ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hsupp : tsupport φ ⊆ Ioo (0:ℝ) 1) :
    let ht : 1-rho≤1 := by linarith
    let f := fun y=>followupEnergyFunctional n β lam rho (parisiMix μ ν y)
    let ζ := responseAveragedCurvatureReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht
    let b := responseMeanHessianReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht
    let Y := ∫q in (0:ℝ)..1,b q*(deriv φ q)^2
    let Z := rho*(∫q : Paper.Overlap,(φ q)^2*
      responseAveragedCurvature (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht q
      ∂(ENNReal.ofReal β • (parisiMix μ ν θ : Measure Paper.Overlap)))
    rho*|∫q in (0:ℝ)..1,(responseProfile ν β q-responseProfile μ β q)*ζ q*φ q|≤
      Real.sqrt (iteratedDeriv 2 f θ/rho)*(Real.sqrt Y+2*Real.sqrt (Y+Z)) := by
  have h0 : φ 0=0 := by
    by_contra hh
    have hs:=hsupp ((subset_tsupport φ) (show 0∈Function.support φ from hh))
    exact (lt_irrefl (0:ℝ)) hs.1
  have h1 : φ 1=0 := by
    by_contra hh
    have hs:=hsupp ((subset_tsupport φ) (show 1∈Function.support φ from hh))
    exact (lt_irrefl (1:ℝ)) hs.2
  let w : ResponseLipschitzTest := ⟨φ,K,hφ,h0,h1⟩
  have hh:=localization_Lipschitz_response_test hn μ ν β lam rho θ hβ hlam hrho hθ w
  dsimp only
  have hsig : responseLipschitzSignal (n:=n) μ ν β (1-rho) lam θ (by linarith) w=
      ∫q in (0:ℝ)..1,(responseProfile ν β q-responseProfile μ β q)*
        responseAveragedCurvatureReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam (by linarith) q*φ q := by
    unfold responseLipschitzSignal responseProfile
    apply intervalIntegral.integral_congr
    intro q _
    dsimp only [w]
    ring
  have hY : responseLipschitzMeanEnergy (n:=n) μ ν β (1-rho) lam θ (by linarith) w=
      ∫q in (0:ℝ)..1,responseMeanHessianReal (n:=n) (parisiMix μ ν θ)
        β (1-rho) lam (by linarith) q*(deriv φ q)^2 := by
    unfold responseLipschitzMeanEnergy ResponseLipschitzTest.slope
    apply intervalIntegral.integral_congr
    intro q _
    dsimp only [w]
    ring
  have hZ : responseLipschitzCurvatureEnergy (n:=n) μ ν β (1-rho) lam θ (by linarith) w=
      rho*(∫q : Paper.Overlap,(φ q)^2*responseAveragedCurvature (n:=n) (parisiMix μ ν θ)
        β (1-rho) lam (by linarith) q ∂(ENNReal.ofReal β • (parisiMix μ ν θ : Measure Paper.Overlap))) := by
    rw [integral_smul_measure,ENNReal.toReal_ofReal hβ.le]
    simp only [responseLipschitzCurvatureEnergy,w,smul_eq_mul,sub_sub_cancel]
    ring
  rw [hsig,hY,hZ] at hh
  exact hh

/-- Endpoint atoms make zero contribution for a genuinely compactly
supported test. This is the literal open-interval Stieltjes convention. -/
theorem compact_support_Stieltjes_integral_interior (φ : ℝ→ℝ)
    (hsupp : tsupport φ ⊆ Ioo (0:ℝ) 1) (ζ : Paper.Overlap→ℝ)
    (m : Measure Paper.Overlap) :
    (∫q : Paper.Overlap,(φ q)^2*ζ q ∂m)=
      ∫q in {q : Paper.Overlap | (q:ℝ)∈Ioo (0:ℝ) 1},(φ q)^2*ζ q ∂m := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  have hz : φ q=0 := by
    by_contra hh
    exact hq (hsupp ((subset_tsupport φ) (show (q:ℝ)∈Function.support φ from hh)))
  simp only [hz,zero_pow (by norm_num : 2≠0),zero_mul]

theorem localization_compact_Lipschitz_response_interior (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β lam rho θ : ℝ)
    (hβ : 0<β) (hlam : 0≤lam) (hrho : 0<rho)
    (hθ : θ∈Ioo (0:ℝ) 1) (φ : ℝ→ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hsupp : tsupport φ ⊆ Ioo (0:ℝ) 1) :
    let ht : 1-rho≤1 := by linarith
    let f := fun y=>followupEnergyFunctional n β lam rho (parisiMix μ ν y)
    let ζ := responseAveragedCurvatureReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht
    let b := responseMeanHessianReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht
    let Y := ∫q in (0:ℝ)..1,b q*(deriv φ q)^2
    let Z := rho*(∫q in {q : Paper.Overlap | (q:ℝ)∈Ioo (0:ℝ) 1},(φ q)^2*
      responseAveragedCurvature (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht q
      ∂(ENNReal.ofReal β • (parisiMix μ ν θ : Measure Paper.Overlap)))
    rho*|∫q in (0:ℝ)..1,(responseProfile ν β q-responseProfile μ β q)*ζ q*φ q|≤
      Real.sqrt (iteratedDeriv 2 f θ/rho)*(Real.sqrt Y+2*Real.sqrt (Y+Z)) := by
  have hh:=localization_compact_Lipschitz_response hn μ ν β lam rho θ
    hβ hlam hrho hθ φ K hφ hsupp
  dsimp only at hh ⊢
  rw [compact_support_Stieltjes_integral_interior φ hsupp] at hh
  exact hh

/-- All segment regularity in Proposition 5.1(b), with genuine ordinary
first and second differentiability in the open parameter interval. -/
theorem localization_segment_regularity_source (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho : ℝ) (hβ : 0<β) (hlam : 0≤lam) (hrho : 0<rho) :
    let f := fun θ=>followupEnergyFunctional n β lam rho (parisiMix μ ν θ)
    ContDiffOn ℝ 2 f (Icc (0:ℝ) 1) ∧
    ContinuousOn f (Icc (0:ℝ) 1) ∧
    ConvexOn ℝ (Icc (0:ℝ) 1) f ∧
    DifferentiableOn ℝ f (Ioo (0:ℝ) 1) ∧
    DifferentiableOn ℝ (deriv f) (Ioo (0:ℝ) 1) := by
  dsimp only
  have hc:=localization_segment_contDiffOn_two hn μ ν β lam rho hβ.ne' hrho
  have ho:=hc.mono Ioo_subset_Icc_self
  refine ⟨hc,hc.continuousOn,?_,ho.differentiableOn (by norm_num),?_⟩
  · exact responseEnergyFunctional_mix_convex n μ ν β (1-rho) lam hβ (by linarith) hlam
  · exact (ho.deriv_of_isOpen isOpen_Ioo (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableOn
      (by norm_num)

end QuantitativeFollowup
