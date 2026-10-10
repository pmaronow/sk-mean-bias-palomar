module
public import QuantitativeFollowup.FollowupCavityDecouplingStepKernel
public import QuantitativeFollowup.FollowupCavityDecouplingSpinTerminal
public import QuantitativeFollowup.FollowupCavityDecouplingProcess

@[expose] public section

/-! Genuine old-spin posterior moments separate at every finite depth and
in the actual arbitrary-profile tail. These are normalized kernel expectations,
not inferred from the one-spin magnetization. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

 theorem anisotropicFiniteFeatureMean_succ_kernel {n : ℕ} (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (f : Configuration n→ℝ) (P : AnisotropicParameter n) :
    anisotropicFiniteFeatureMean D s (j+1) f P=
      ∫Q,anisotropicFiniteFeatureMean D s j f Q ∂anisotropicDepthKernel D s j P := by
  rw [anisotropicFiniteFeatureMean_eq_futureKernels,OverlapPaper.sourceKernelExpectation]
  simp_rw [←anisotropicFiniteFeatureMean_eq_futureKernels]

 theorem cavityFiniteRestFeature_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (f : Configuration n→ℝ)
    (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) s j
      (fun σ=>f (cavityRestConfiguration σ)) P=
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j f
        (cavityRestParameterProjection n P) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  induction j generalizing P with
  | zero =>
    let g : AnisotropicDisorder (n+1):=WithLp.toLp 2 (fun e=>P (Sum.inl e))
    let x : QuantitativePaper.Field (n+1):=WithLp.toLp 2 (fun i=>P (Sum.inr i))
    have hid : anisotropicParameterPoint g x=P :=by ext i;cases i <;> rfl
    rw [←hid,cavityRestParameterProjection_point,anisotropicFiniteFeatureMean_zero,anisotropicFiniteFeatureMean_zero]
    exact cavityTerminalRestFeature_zero n β ρ hβ hρ g x f
  | succ j ih =>
    let g : AnisotropicDisorder (n+1):=WithLp.toLp 2 (fun e=>P (Sum.inl e))
    let x : QuantitativePaper.Field (n+1):=WithLp.toLp 2 (fun i=>P (Sum.inr i))
    have hid : anisotropicParameterPoint g x=P :=by ext i;cases i <;> rfl
    rw [anisotropicFiniteFeatureMean_succ_kernel,anisotropicFiniteFeatureMean_succ_kernel]
    simp_rw [ih]
    have hF:=measurable_anisotropicFiniteFeatureMean R s j f
    rw [←integral_map (cavityRestParameterProjection n).measurable.aemeasurable hF.aestronglyMeasurable]
    rw [←hid,cavityDepthKernel_rest_zero,cavityRestParameterProjection_point]

 theorem cavityFiniteRestPairResponse_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (P : AnisotropicParameter (n+1)) (e : AnisotropicCouplingIndex n) :
    anisotropicFiniteTailPairResponse
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) s q P
      (cavityRestCouplingEmbedding n e)=
      anisotropicFiniteTailPairResponse (followupCavityRestSpinModel n β ρ hβ hρ) s q
        (cavityRestParameterProjection n P) e := by
  rw [anisotropicFiniteTailPairResponse_eq_spinMoment,anisotropicFiniteTailPairResponse_eq_spinMoment]
  have hf:=cavityFiniteRestFeature_zero (vectorClampedScheme s q q.property) n β ρ hβ hρ (k+2)
    (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) P
  exact hf

 theorem cavityRestTailPairResponse_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (P : AnisotropicParameter (n+1)) (e : AnisotropicCouplingIndex n) :
    anisotropicTailPairResponse
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q P
      (cavityRestCouplingEmbedding n e)=
      anisotropicTailPairResponse (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (cavityRestParameterProjection n P) e := by
  have hfull:=tendsto_anisotropicFiniteTailPairResponse_moving
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ
    (cavityRestCouplingEmbedding n e) (tendsto_const_nhds (x:=q)) (tendsto_const_nhds (x:=P))
  simp_rw [cavityFiniteRestPairResponse_zero] at hfull
  exact tendsto_nhds_unique hfull (tendsto_anisotropicFiniteTailPairResponse_moving
    (followupCavityRestSpinModel n β ρ hβ hρ) μ e
    (tendsto_const_nhds (x:=q)) (tendsto_const_nhds (x:=cavityRestParameterProjection n P)))

end QuantitativeFollowup
