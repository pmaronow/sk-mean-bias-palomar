module
public import QuantitativeFollowup.ScalarResponseNormBounds
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

@[expose] public section

/-! An actual profile-uniform L² bound for the literal scalar response,
proved from its genuine bounded coefficients and integral Cauchy--Schwarz. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def scalarResponseL2Bound (β : ℝ) : ℝ := 12*β^2*scalarResponseKernelBound β

theorem scalarResponseL2Bound_nonneg (β : ℝ) : 0 ≤ scalarResponseL2Bound β := by
  dsimp only [scalarResponseL2Bound,scalarResponseKernelBound]
  positivity

theorem continuousMap_norm_sq_toLp (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (φ : C(Paper.Overlap,ℝ)) :
    ‖ContinuousMap.toLp 2 ν ℝ φ‖^2=∫q : Paper.Overlap,φ q^2 ∂ν := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp (p:=2) (μ:=ν) (𝕜:=ℝ)] with q hq
  change inner ℝ ((ContinuousMap.toLp 2 ν ℝ φ) q) ((ContinuousMap.toLp 2 ν ℝ φ) q)=φ q^2
  rw [hq]
  simp [pow_two]

theorem scalar_response_L2_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : C(Paper.Overlap,ℝ)) :
    ‖ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ
      (scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩)‖ ≤ 
        scalarResponseL2Bound β*‖ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ‖ := by
  let ν := parisiFreeMeasure μ a
  let J := scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩
  let C : ℝ := 6*β^2*scalarResponseKernelBound β
  let massNorm : ℝ := ∫q,|φ q| ∂ν
  let S : ℝ := ∫q,φ q^2 ∂ν
  have hC : 0 ≤ C := by dsimp only [C,scalarResponseKernelBound];positivity
  have hI : 0 ≤ massNorm := integral_nonneg fun q=>abs_nonneg _
  have hS : 0 ≤ S := integral_nonneg fun q=>sq_nonneg _
  have hf : MemLp (fun q : Paper.Overlap=>|φ q|) 2 ν := by
    exact (φ.continuous.abs).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCS := integral_sq_le_mass_mul_integral_sq (fun q : Paper.Overlap=>|φ q|) hf
  simp only [sq_abs] at hCS
  have hIsq : massNorm^2 ≤ S := hCS.trans (mul_le_of_le_one_left hS (scalarFreeMeasure_mass_le_one μ a ha))
  have hpoint (q : Paper.Overlap) : J q^2 ≤ 2*C^2*(φ q^2+massNorm^2) := by
    have hp := scalar_response_norm_pointwise β hβ μ a ha φ q
    change |J q| ≤ C*(|φ q|+massNorm) at hp
    have hsq := pow_le_pow_left₀ (abs_nonneg (J q)) hp 2
    simp only [sq_abs] at hsq
    have haux : (|φ q|+massNorm)^2 ≤ 2*(φ q^2+massNorm^2) := by nlinarith [sq_nonneg (|φ q|-massNorm),sq_abs (φ q)]
    nlinarith [mul_le_mul_of_nonneg_left haux (sq_nonneg C)]
  have hφsq : Integrable (fun q : Paper.Overlap=>φ q^2) ν :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJsq : Integrable (fun q : Paper.Overlap=>J q^2) ν :=
    (J.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound := integral_mono hJsq ((hφsq.add (integrable_const _)).const_mul (2*C^2)) hpoint
  rw [integral_const_mul] at hbound
  simp only [Pi.add_apply] at hbound
  rw [integral_add hφsq (integrable_const _),integral_const,smul_eq_mul] at hbound
  have hm : ν.real univ*massNorm^2 ≤ massNorm^2 := mul_le_of_le_one_left (sq_nonneg massNorm) (scalarFreeMeasure_mass_le_one μ a ha)
  have hsq : (∫q : Paper.Overlap,J q^2 ∂ν) ≤ (2*C)^2*S := by nlinarith
  have heJ := continuousMap_norm_sq_toLp ν J
  have heφ := continuousMap_norm_sq_toLp ν φ
  change ‖ContinuousMap.toLp 2 ν ℝ J‖ ≤ scalarResponseL2Bound β*‖ContinuousMap.toLp 2 ν ℝ φ‖
  have hfac : scalarResponseL2Bound β=2*C := by dsimp only [scalarResponseL2Bound,C];ring
  rw [hfac]
  dsimp only [S] at hsq
  rw [←heJ,←heφ] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  simpa only [mul_pow] using hsq

end QuantitativeFollowup
